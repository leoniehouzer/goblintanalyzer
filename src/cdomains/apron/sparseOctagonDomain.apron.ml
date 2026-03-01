(** OCaml implementation of the sparse octagon domain.

    @see <http://doi.acm.org/NOTYETPUBLISHED>  M. Petter, and H. Seidl Sparse Octagons. *)

open Batteries
open GoblintCil
open Pretty
module M = Messages
open GobApron

module Mpqf = SharedFunctions.Mpqf

exception Bot
type 'v lit = Pos of 'v | Neg of 'v [@@deriving hash]
let negate = function
  | Pos v -> Neg v
  | Neg v -> Pos v

type 'v comb = Unary of 'v lit | Binary of 'v lit * 'v lit

let string_of_lit f = function
  | Pos v -> "+" ^ f v
  | Neg v -> "-" ^ f v

(** Variable
 * type t, basically ordered and printable
*)
module type Carrier = sig (* defines the module Carrier *)
  type t [@@deriving hash]
  val compare : t -> t -> int
  val string_of : t -> string
  val to_int : t -> int (*neu*)
  val to_t : int -> t (*neu*)
end

(** Literal, i.e. +var or -var
 *  ordered and printable
*)
module Lit (C : Carrier) = struct (* implement the functor Lit *)
  type t = C.t lit [@@deriving hash] 
  let compare a b = match a, b with
    | Pos x, Pos y
    | Neg x, Neg y -> C.compare x y
    | Pos x, Neg y -> 1
    | Neg x, Pos y -> -1
  let string_of lit = string_of_lit C.string_of lit
  let hash = function
  | Pos v -> Hashtbl.hash (1, C.hash v)
  | Neg v -> Hashtbl.hash (0, C.hash v)

  let to_int (i : t) : int = match i with
    | Pos v -> C.to_int v
    | Neg v -> C.to_int v
  let to_t (i : int) = Pos (C.to_t i)
end

(**
 * Pair of literals, i.e. (+var, +var) or (+var, -var)
 * ordered and printable
*)
module Pair (C : Carrier) (C : Carrier) = struct
  type t = C.t * C.t [@@deriving hash]
  let compare (a1, a2) (b1, b2) = match C.compare a1 b1 with
    | 0 -> C.compare a2 b2
    | x -> x
  let string_of (v1,v2) = C.string_of v1 ^ C.string_of v2
end


(**
 * Octagon module
 * - maps Literals and Pairs to their upper bounds wrt ≤
 * - internally maps Literals to their set of influencing Literals
*)
module Oct (Carrier : Carrier) = struct (* functor *)

  module LitV = Lit (Carrier) (* defines the module LitV by using the functor Lit *)
  module PairLV = Pair (LitV) (LitV)
  module UnaryMap = Map.Make(LitV)
  module BinaryMap = Map.Make(PairLV)
  module VarSet = Set.Make(Carrier)
  module LitSet = Set.Make(LitV)
  module PairSet = Set.Make(PairLV)

  (** t encodes a valid octagon. oct leaves room for none as bottom *)
  type t = {
    unary: int UnaryMap.t; 
    binary: int BinaryMap.t;
    infl: LitSet.t UnaryMap.t
  } [@@deriving eq,ord]

  let is_top {unary; binary; infl} =
    UnaryMap.is_empty unary && BinaryMap.is_empty binary && UnaryMap.is_empty infl

  (** exception Bot is raised if the octagon is inconsistent, i.e. contains a constraint that is not satisfiable *)

  (** reorder pairs so that the variable order is met *)
  let normal = function
    | (v1,v2) -> if LitV.compare v1 v2 <= 0 then (v1,v2)
      else (v2,v1)
      
  (** implements map[v] ← (map[v] ⊔ b) and returns (status, map)
   *  status = None: new entry, Some false: no change, Some true: change 
  *)
  let add_min map v b = 
    match UnaryMap.find_opt v map with 
    | None -> let map = UnaryMap.add v b map in 
      (None, map)
    | Some b0 -> if b >= b0 then (Some false, map)
      else let map = UnaryMap.add v b map in
        (Some true, map)

  (** implements map[(v1,v2)] ← (map[(v1,v2)] ⊔ b) and returns (status, map)
   *  status = None: new entry, Some false: no change, Some true: change 
  *)
  let add2_min map p b = 
    match BinaryMap.find_opt p map with 
    | None -> let map = BinaryMap.add p b map in 
      (None, map)
    | Some b0 -> if b >= b0 then (Some false, map)
      else let map = BinaryMap.add p b map in
        (Some true, map)

  (** consistency check 1: v ≤ b  ∧  -v ≤ b' ⇒ 0 ≤ b+b'*)
  let check1 map v b = match UnaryMap.find_opt (negate v) map with
    | None -> ()
    | Some b' ->  if 0 > b+b' then raise Bot

  (** consistency check 2: lit1+lit2 ≤ b  ∧  -lit1-lit2 ≤ b' ⇒ 0 ≤ b+b'*)
  let check2 map (v1,v2) b = match BinaryMap.find_opt (normal (negate v1, negate v2)) map with
    | None -> ()
    | Some b' -> if 0 > b+b' then raise Bot

  (* FUNCTIONS FOR INFL: *)

  (** add a binary boundary motivated dependency to infl from v1 to v2, i.e. for infl[v1] ← infl[v1] ∪ v2 
   * precondition: v1 < v2  
  *)
  let add_elem v1 v2 infl = match UnaryMap.find_opt v1 infl with
    | None -> UnaryMap.add v1 (LitSet.singleton v2) infl
    | Some set -> UnaryMap.add v1 (LitSet.add v2 set) infl

  (** remove a binary boundary motivated dependency to infl from v1 to v2, i.e. infl[v1] ← infl[v1] ∖ v2 
   * precondition: v1 < v2  
  *) 
  let rem_elem v1 v2 infl = match UnaryMap.find_opt v1 infl with
    | None -> infl
    | Some set -> let set = LitSet.remove v2 set in
      if LitSet.is_empty set then UnaryMap.remove v1 infl
      else UnaryMap.add v1 set infl

  (** rebuild the influence graph from the binary bounds map *)
  let rebuild_infl binary = (* über binary iterieren, und beide richtungen zu "leerer" infl hinzufügen *)
  (* TODO: werden beide richtungen gespeichert? überlegen! achtung auch bei der precondition von add_elem *)
    BinaryMap.fold (
      fun (lit1, lit2) _ new_infl -> add_elem lit2 lit1 (add_elem lit1 lit2 new_infl)
    ) binary UnaryMap.empty  


  let var_of_lit = function
    | Pos v | Neg v -> v

  (** initialize the octagon consistently with the given list of constraints list, starting from 
    * - unary bounds map m1
    * - binary bounds map m2 
    * - influence graph infl 
    * creating a constistent set of occuring variables, set
  *)
  let init (m1, m2, infl) (list : (Carrier.t comb * int) list) =
    let set = VarSet.empty in
    List.fold_left (fun (set, m1, m2, infl) ((comb : Carrier.t comb),b) -> match comb with
        | Binary (v1, v2) -> let p = normal (v1, v2) in (* normalizing pair, s.t. v1 < v2 *)
          (match add2_min m2 p b with (* add binary variable bound, sensitive about actual change *)
           | Some false, m2 -> set,m1,m2,infl (* entry present, but no change *)
           | Some true, m2 ->                 (* entry present, tighter bounds *)
             (check2 m2 p b;                     (* bottom check necessary, since bounds tightened *)
              (set, m1,m2,infl))
           | None, m2 ->                      (* no entry yet *)
             (check2 m2 p b;                      (* bottom check necessary, since new bounds established *)
              let set = VarSet.add (var_of_lit v1) set in
              let set = VarSet.add (var_of_lit v2) set in
              let infl = add_elem v1 v2 infl in (* add influences from v1 to v2 and vice versa *)
              let infl = add_elem v2 v1 infl in
              (set,m1,m2,infl)
             )
          )
        | Unary v -> (match add_min m1 v b with
            | _,m1 -> set, m1, m2, infl (* add unary variable bound, not caring about change *)
          )
      ) (set, m1, m2, infl) list

  (** check if the binary constraint (v1,v2) ≤ b is subsumed by the unary constraints from m1, 
   * i.e. v1 ≤ b1  ∧  v2 ≤ b2  ∧  b1+b2 ≤ b
  *)
  let subsumed m1 (v1,v2) b = match UnaryMap.find_opt v1 m1, UnaryMap.find_opt v2 m1 with
    | None, None
    | None, Some _
    | Some _, None  -> false
    | Some b1, Some b2 -> (b1 + b2 <= b)

  (** optimize the octagon by removing subsumed binary constraints, including their influence
   * returns the optimized influence graph and the optimized binary bounds map
  *)
  let optimize m1 m2 infl = BinaryMap.fold (fun (v1, v2) b (infl,m) ->
      if subsumed m1 (v1, v2) b then 
        (rem_elem v1 v2 infl |>
         rem_elem v2 v1),
        BinaryMap.remove (v1, v2) m
      else infl,m
    ) m2 (infl,m2) 

  (** iterate over all pairs of elements in l1 and l2, applying f to each pair *)
  let iterate2 f a l1 l2 = List.fold_left (fun a x1 ->
      List.fold_left (fun a x2 -> f a x1 x2) a l2) a l1

  (** Closure provided by following the binary constraints through chains of x/-x occuring in some lhs of a oct-constraint*)
  let propagate2 (set, m1, m2, infl) = VarSet.fold (fun x (m1, m2, infl) ->
      match UnaryMap.find_opt (Pos x) infl, UnaryMap.find_opt (Neg x) infl with (* find all influences for x and -x *)
      | None,_
      | _,None -> m1, m2, infl
      | Some pl, Some nl -> 
        let pl = LitSet.elements pl in (* convert sets of  x influenced Literals to lists *)
        let nl = LitSet.elements nl in (* convert sets of -x influenced Literals to lists *)
        iterate2 (fun (m1, m2, infl) v1 v2 -> (* iterate on crossproduct of the influenced lists, v1 positive, v2 negative *)
            let p1 = normal (Pos x, v1) in (* setup normalized pairs, connected via pos/neg x *)
            let p2 = normal (Neg x, v2) in
            match BinaryMap.find_opt p1 m2, BinaryMap.find_opt p2 m2 with (* lookup the bounds b1, b2 for these pairs *)
            | None, _  
            | _, None -> failwith (Carrier.string_of x ^ " :\t" ^ string_of_lit Carrier.string_of v1 ^ string_of_lit Carrier.string_of v2 ^ "\n m2 should have value for p1!")
            | Some b1, Some b2 -> let b = b1 + b2 in (* calculate the bound b for v1+v2 ≤ b*)
              (* checks and updates *)
              if v1 = negate v2 then (* we connected x-y ≤ b1 and y-x ≤ b2 *)
                if b < 0 then raise Bot (* bottom check, due to y-y < 0 *)
                else m1, m2, infl
              else if v1 = v2 then   (* we connected x+y ≤ b1 and x-y ≤ b2  ⇒ 2y ≤ b *)
                let b = b/2 in (match add_min m1 v1 b with (*  add y ≤ b/2  *)
                    | Some false, m1 -> m1, m2, infl
                    | None, m1
                    | Some true, m1 -> check1 m1 v1 b;
                      (m1, m2, infl))
              else (* v1 ≠ v2 and v1 ≠ -v2 *) 
                let p = normal (v1, v2) in
                (match add2_min m2 p b with (* add v1+v2 ≤ b *)
                 | Some false, m2 -> m1, m2, infl
                 | Some true, m2 -> check2 m2 p b;
                   (m1, m2, infl)
                 | None, m2 -> check2 m2 p b; 
                   let infl = add_elem v1 v2 infl in
                   let infl = add_elem v2 v1 infl in
                   m1, m2, infl
                )) (m1, m2, infl) pl nl) set (m1, m2, infl) 

  let rec propagate1_aux l (m1, m2, infl) = match l with (* deconstruct all unary constraints into (x ≤ b) :: l *)
    | [] -> m1
    | (v, b) :: l -> (match UnaryMap.find_opt (negate v) infl with (* for x find all influences of -x *)
        | None -> propagate1_aux l (m1, m2, infl)    (* no influences, continue munching list l*)
        | Some set -> let m1 = LitSet.fold (fun v1 m1 -> 
            let p = normal (negate v, v1) in 
            (match BinaryMap.find_opt p m2 with (* checkout all y-x ≤ b1 *)
             | None -> m1
             | Some b1 -> (match add_min m1 v1 (b + b1) with
                 | Some false, m1 -> m1 
                 | Some true, m1
                 | None, m1-> check1 m1 v1 (b + b1); m1
               ))) set m1 in
          propagate1_aux l (m1, m2, infl) (* continue munching list l*)
      )

  (**
   * Propagate unary constraints through the octagon, i.e. for each x ≤ b, check all y-x ≤ b' and update unaries with y ≤ b+b'
  *)
  let propagate1 (m1, m2, infl) = propagate1_aux (UnaryMap.bindings m1) (m1, m2, infl)

  (** enrich binary bounds by summing up unaries *)
  let complete {unary; binary; infl} = 
    let l1 = UnaryMap.bindings unary in (* l1 = list of all unary bounds *)
    let binary, infl = (* cross-product of all unary bounds *)
      List.fold_left (fun (m2, infl) (v1, b1) ->
          List.fold_left (fun (m2, infl) (v2, b2) -> (* ignore same-variable bounds *)
              if      LitV.compare v1         v2  = 0 then (m2, infl)
              else if LitV.compare v1 (negate v2) = 0 then (m2, infl)
              else
                let p = normal (v1, v2) in (* synthesize binary constraints from unary ones *)
                match add2_min m2 p (b1 + b2) with  (* collect v1+v2 ≤ b1 + b2 *)
                | None, m2 -> 
                  let infl = add_elem v1 v2 infl in
                  let infl = add_elem v2 v1 infl in
                  check2 m2 p (b1 + b2); (* probably, superfluous! *)
                  m2, infl
                | Some false, m2 -> m2, infl
                | Some true, m2 -> check2 m2 p (b1 + b2); (* probably, superfluous! *)
                  m2, infl)
            (m2, infl) l1) 
        (binary, infl) l1 in
    {unary; binary; infl}
  
  let strong_closure oct = 
    let oct = complete oct in (* first enrich binary bounds by summing up unaries *)
    let (m1, m2, infl) = propagate2 (VarSet.of_list (List.map (fun (v, _) -> var_of_lit v) (UnaryMap.bindings oct.unary)), oct.unary, oct.binary, oct.infl) in (* then propagate binary bounds through the octagon *)
    let m1 = propagate1 (m1, m2, infl) in (* finally, propagate unary bounds through the octagon *)
    {unary = m1; binary = m2; infl}

  (** 
   * Create an octagon from a list of constraints;
   * 1. Initialize the octagon with empty maps
   * 2. Import list of constraints and check for consistency
   * 3. Interconnect binary constraints Floyd-Warshall-Style through the octagon
   * 4. Propagate unary constraints through the octagon
   * 5. Optimize the octagon by removing subsumed binary constraints
  *)
  let of_list (list : (Carrier.t comb * int) list) =  try
      let m1 = UnaryMap.empty in
      let m2 = BinaryMap.empty in
      let infl = UnaryMap.empty in
      let (set, m1, m2, infl) = init (m1, m2, infl) list in
      let (m1, m2, infl) = propagate2 (set, m1, m2, infl) in
      let m1 = propagate1 (m1, m2, infl) in
      let infl,m2 = optimize m1 m2 infl in
      Some {unary = m1; binary = m2; infl}
    with Bot -> None
  (* Alternatively, store the show function 'v -> string inside the octagon and then use
    let comp v1 v2 = String.compare (show v1) (show v2)
    Only disadvantage: this requires a lot of string manipulation ... *)

  (** removes all constraints with +x or -x in binary, but adds the one that hold implicitly; returns the new unary and binary *)
    let forget_var_binary x unary binary infl = 
      match UnaryMap.find_opt (Pos x) infl, UnaryMap.find_opt (Neg x) infl with
      | None,_ | _,None -> (unary, BinaryMap.filter (fun (v1, v2) _ -> v1 <> Pos x && v1 <> Neg x && v2 <> Pos x && v2 <> Neg x) binary, infl) (* remove all constraints with +x or -x*)
      | Some pl, Some nl -> (* pl = set of literals, that are connected with Pos x, nl = for Neg x *)
        let pl = LitSet.elements pl in (* convert sets of +x influenced Literals to lists *)
        let nl = LitSet.elements nl in (* convert sets of -x influenced Literals to lists *)
        iterate2 (fun (unary, binary, infl) v1 v2 -> (* iterate on crossproduct of the influenced lists, v1 positive, v2 negative *)
          let p1 = normal (Pos x, v1) in (* setup normalized pairs, connected via pos/neg x *)
          let p2 = normal (Neg x, v2) in
          (* Annahme: die Pairs sind immer in normalized order gespeichert *)
          match BinaryMap.find_opt p1 binary, BinaryMap.find_opt p2 binary with (* lookup the bounds b1, b2 for these pairs *)
          | None, _  | _, None -> failwith "cant happen, bc there should be a binary constraint, since it is in the influence graph"
          | Some b1, Some b2 -> 
            let binary = BinaryMap.remove p1 (BinaryMap.remove p2 binary) in (* remove the constraints with x and -x *) (* TODO: evtl. auch aus infl entfernen *)
            let b = b1 + b2 in (* calculate the bound b for v1+v2 ≤ b*)
            if v1 = negate v2 then (* Case: we connected +x-y ≤ b1 and -x+y ≤ b2 ⇒ -y+y ≤ b ⇒ 0 ≤ b ⇒ if b is negative then error, else do nothing *)
              if b < 0 then raise Bot 
              else (unary, binary, infl)
            else if v1 = v2 then   (* Case: we connected x+y ≤ b1 and -x+y ≤ b2 ⇒ y+y ≤ b ⇒ 2y ≤ b ⇒ y ≤ b/2 in unary speichern *)
              let b = b/2 in
              (match add_min unary v1 b with (* add y ≤ b/2 *) 
                | Some false, unary -> (unary, binary, infl) (* new entry *)
                | None, unary (* entry present, but no change *) | Some true, unary (* entry changed *) -> check1 unary v1 b; (unary, binary, infl))
            else (* Case: we connected two different variables v1, v2 *) 
              let p = normal (v1, v2) in
              (match add2_min binary p b with (* add v1+v2 ≤ b *)
                | Some false, binary -> (unary, binary, infl) (* entry present, but no change *)
                | Some true, binary (* entry changed *) -> check2 binary p b; (unary, binary, infl)
                | None, binary (* new entry *) -> check2 binary p b;
                  let infl = add_elem v1 v2 infl in
                  let infl = add_elem v2 v1 infl in 
                  (unary, binary, infl)
                )
        ) (unary,binary, infl) pl nl
              
  (** Remove all bounds that relate to a variable x from oct i.e. [[x := ?]] *)
  let forget_var x oct =
    match oct with
    | None -> None
    | Some {unary; binary; infl} -> (
      let new_unary = (UnaryMap.remove (Pos x) (UnaryMap.remove (Neg x) unary)) in
      let (new_unary, new_binary, infl) = forget_var_binary x new_unary binary infl in
      Some {unary = new_unary ; binary = new_binary; infl = (rebuild_infl new_binary)}) (* TODO: muss evtl. subsumed aufgerufen werden?*)

  let list_of = function 
    | None -> None
    | Some {unary; binary; infl} -> Some (
        BinaryMap.bindings binary |>
        List.map (fun ((v1, v2), b) -> (Binary (v1, v2), b)) |> 
        UnaryMap.fold (fun v b list -> (Unary v, b) :: list) unary 
      )

  let string_of_constr f = function
    | Unary v,b -> string_of_lit f v ^ " <= " ^ string_of_int b
    | Binary (v1,v2),b -> string_of_lit f v1 ^ string_of_lit f v2 ^ " <= " ^ string_of_int b  
  let string_of_constraints f list = 
    String.concat "" (
      List.map (fun c -> "\t" ^ string_of_constr f c ^ "\n") list)
  let string_of oct = match list_of oct with
    | None -> "\t⊥\n"
    | Some  list -> string_of_constraints Carrier.string_of list

  (* AbstractRelationalDomainRepresentation duties: *)
  let copy = Fun.id
  let hash {unary; binary; infl} =
    let h1 = UnaryMap.fold (fun k value acc -> 13*13 * acc+ 31* LitV.hash k + value) unary in
    let h2 = BinaryMap.fold (fun k value acc -> 13*13 * acc+ 31* PairLV.hash k + value) binary in
    Hashtbl.hash (h1, h2) (* do we need to hash infl as well?*)
  let empty () = {unary = UnaryMap.empty; binary = BinaryMap.empty; infl = UnaryMap.empty}
  let is_empty o = true


  (* HELPER FUNCTIONS FOR DIM_ADD *)
  (* Map: fold f m init computes (f kN dN ... (f k1 d1 init)...), where k1 ... kN are keys, and d1 ... dN are associated data *)
  (* List: fold_left f startwert [x1; x2; ...; xn] bedeutet: f ( ... (f (f startwert x1) x2) ... ) xn *)
  (* Achtung: bei Map zuerst map, dann startwert, bei list is es anders herum *)
  
  let shift_index_add (old_index : Carrier.t) (occ_cols : (int * int) list) : Carrier.t = 
    (* finde in occ_cols alle eintäge kleiner gleich old_index und zähle sie (=k), dann new_index = old_index + k , return new_index *)
    let k = List.fold_left (
      fun acc (index, count) -> if index <= (Carrier.to_int old_index) then acc + count else acc 
      ) 0 occ_cols
    in let new_index = (Carrier.to_int old_index) + k 
    in Carrier.to_t new_index 

  let dim_add (ch: Apron.Dim.change) o =
    let cols_list = Array.to_list ch.dim in
    let grouped_indices = List.group Int.compare cols_list in
    let occ_cols = List.map (fun group -> ((List.hd group, List.length group))) grouped_indices in 
    (* Ansatz aus listMatrix.ml, add_empty_columns; Bsp.: cols_list = [1; 3; 3; 5] -> grouped_indices = [[1]; [3; 3]; [5]] -> occ_cols = [(1, 1); (3, 2); (5, 1)] *)
    let new_unary = (
      UnaryMap.fold (fun old_lit bound new_unary -> 
          match old_lit with
          | Pos old_index -> UnaryMap.add (Pos (shift_index_add old_index occ_cols)) bound new_unary
          | Neg old_index -> UnaryMap.add (Neg (shift_index_add old_index occ_cols)) bound new_unary
      ) o.unary UnaryMap.empty ) 
    in 
    let new_binary = (
      BinaryMap.fold (fun (old_lit1, old_lit2) bound new_binary -> 
          let new_lit1 = match old_lit1 with
            | Pos old_index1 -> Pos (shift_index_add old_index1 occ_cols)
            | Neg old_index1 -> Neg (shift_index_add old_index1 occ_cols)
          in
          let new_lit2 = match old_lit2 with
            | Pos old_index2 -> Pos (shift_index_add old_index2 occ_cols)
            | Neg old_index2 -> Neg (shift_index_add old_index2 occ_cols)
          in
          BinaryMap.add (new_lit1, new_lit2) bound new_binary
      ) o.binary BinaryMap.empty )
    in
    { unary = new_unary; binary = new_binary; infl = (rebuild_infl new_binary) } 


  (* HELPER FUNCTIONS FOR DIM_REMOVE *)
  let shift_index_remove (old_index : Carrier.t) (dim_list : int list) : Carrier.t = 
    let k = List.fold_left (
      fun acc index -> if index < (Carrier.to_int old_index) then acc + 1 else acc 
    ) 0 dim_list
    in let new_index = (Carrier.to_int old_index) - k 
    in Carrier.to_t new_index 

  (* iteriert über liste zu löschender variablen *)
  let new_unary_remove1 unary (dim_list : int list) = 
    List.fold_left (fun new_unary x -> UnaryMap.remove (Pos (Carrier.to_t x)) (UnaryMap.remove (Neg (Carrier.to_t x)) new_unary)) unary dim_list 

  (* iteriert über unary map *)
  let new_unary_remove2 old_unary (dim_list : int list) = 
    UnaryMap.fold (fun old_lit bound new_unary -> 
        match old_lit with
        | Pos old_index -> if List.mem (Carrier.to_int old_index) dim_list then new_unary else UnaryMap.add (Pos old_index) bound new_unary
        | Neg old_index -> if List.mem (Carrier.to_int old_index) dim_list then new_unary else UnaryMap.add (Neg old_index) bound new_unary
    ) old_unary UnaryMap.empty  

  (* Remove binary constraints, where both variables are removed *)
  let binary_remove1 old_binary (dim_list : int list) =
    BinaryMap.fold (fun (old_lit1, old_lit2) bound new_binary -> 
      match (old_lit1, old_lit2) with
      | (Neg old_index1, Neg old_index2) -> 
        if List.mem (Carrier.to_int old_index1) dim_list && List.mem (Carrier.to_int old_index2) dim_list then new_binary (* constraint "löschen" *)
        else BinaryMap.add (Neg old_index1, Neg old_index2) bound new_binary (* constraint behalten *)
      | (Neg old_index1, Pos old_index2) ->
        if List.mem (Carrier.to_int old_index1) dim_list && List.mem (Carrier.to_int old_index2) dim_list then new_binary (* constraint "löschen" *)
        else BinaryMap.add (Neg old_index1, Pos old_index2) bound new_binary (* constraint behalten *)
      | (Pos old_index1, Neg old_index2) ->
        if List.mem (Carrier.to_int old_index1) dim_list && List.mem (Carrier.to_int old_index2) dim_list then new_binary (* constraint "löschen" *)
        else BinaryMap.add (Pos old_index1, Neg old_index2) bound new_binary (* constraint behalten *)
      | (Pos old_index1, Pos old_index2) ->
        if List.mem (Carrier.to_int old_index1) dim_list && List.mem (Carrier.to_int old_index2) dim_list then new_binary (* constraint "löschen" *)
        else BinaryMap.add (Pos old_index1, Pos old_index2) bound new_binary (* constraint behalten *)
    ) old_binary BinaryMap.empty 
  
  (* ändert nur die Indizes in binary für remove, aber löscht nichts *)
  let dim_remove_rename unary binary (dim_list : int list) =
    (UnaryMap.fold (fun old_lit bound new_unary -> 
        let new_lit = match old_lit with
          | Pos old_index -> Pos (shift_index_remove old_index dim_list)
          | Neg old_index -> Neg (shift_index_remove old_index dim_list)
    in UnaryMap.add new_lit bound new_unary
    ) unary UnaryMap.empty) ,
    (BinaryMap.fold (fun (old_lit1, old_lit2) bound new_binary -> 
        let new_lit1 = match old_lit1 with
          | Pos old_index1 -> Pos (shift_index_remove old_index1 dim_list)
          | Neg old_index1 -> Neg (shift_index_remove old_index1 dim_list)
        in
        let new_lit2 = match old_lit2 with
          | Pos old_index2 -> Pos (shift_index_remove old_index2 dim_list)
          | Neg old_index2 -> Neg (shift_index_remove old_index2 dim_list)
      in BinaryMap.add (new_lit1, new_lit2) bound new_binary
    ) binary BinaryMap.empty)

  let dim_remove (ch: Apron.Dim.change) o = 
    let dim_list = Array.to_list ch.dim |> List.sort_uniq Int.compare in (* Duplikate entfernen *)
    let unary =  new_unary_remove2 o.unary dim_list in (* TODO: verison 1 oder 2 verwenden? *)
    let binary = binary_remove1 o.binary dim_list in
    let infl = rebuild_infl binary in
    let (new_unary, new_binary, new_infl) = List.fold_left (fun (unary, binary, infl) x -> forget_var_binary (Carrier.to_t x) unary binary infl) (unary, binary, infl) dim_list in 
    let (new_unary, new_binary) = dim_remove_rename new_unary new_binary dim_list in
    let (optimized_infl, optimized_binary) = optimize new_unary new_binary (rebuild_infl new_binary) in
    { unary = new_unary; binary = optimized_binary; infl = optimized_infl }
end

(** [VarManagement] defines the type t of the sparse octagon domain (a record that contains an optional octagon and an apron environment) 
        and provides the functions needed for handling variables (which are defined by [RelationDomain.D2]) such as [add_vars], [remove_vars].
*)
module VarManagement =
struct
  module IntBased = struct
    type t = int [@@deriving eq, ord, hash]
    let string_of i = 
      let to_subscript i =
        let transl = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|] in
        let rec subscr i =
          if i = 0 then ""
          else (subscr (i/10)) ^ transl.(i mod 10) in
        subscr i in
      "x"^to_subscript i
    let to_int (i : t) : int = i
    let to_t (i : int) : t = i
  end
  module SparseOctagon = Oct(IntBased)
  include SharedFunctions.VarManagementOps (SparseOctagon)

end

module ExpressionBounds: (SharedFunctions.ConvBounds with type t = VarManagement.t) =
struct
  include VarManagement
  let bound_texpr t texpr = failwith "SparseOctagonDomain.bound_texpr: not implemented"

end

module D =
struct
  include Printable.Std
  include RatOps.ConvenienceOps (Mpqf)
  include VarManagement

  module Bounds = ExpressionBounds
  module V = RelationDomain.V
  module Arg = struct
    let allow_global = true
  end
  module Convert = SharedFunctions.Convert (V) (Bounds) (Arg) (SharedFunctions.Tracked)
  let name () = "sparseOctagon"
  let to_yojson _ = failwith "SparseOctagonDomain.to_yojson: not implemented"
  (* pretty printing *)
  let show a = SparseOctagon.string_of a.d
  let pretty () x = text (show x)
  let pretty_diff () (x, y) = dprintf "%s: %a ≰ %a" (name ()) pretty x pretty y
  let printXml f x = BatPrintf.fprintf f "<value>\n<map>\n<key>\ninequalities\n</key>\n<value>\n%s</value>\n<key>\nenv\n</key>\n<value>\n%a</value>\n</map>\n</value>\n" (XmlUtil.escape (show x)) Environment.printXml x.env

  (* ********************** *)
  (* basic lattice handling *)
  (* ********************** *)

  let top () = {d= Some (SparseOctagon.empty ()); env = empty_env }
  let is_top t = match t.d with
    | None -> false
    | Some d -> SparseOctagon.is_top d
  let is_bot t = equal t (bot ())

  (* *************************** *)
  (* domain specific support code *)
  (* *************************** *)

  (** oct ⊓ constraintlist implemented as a continuation of init *)
  let cap_list ({unary; binary; infl} : SparseOctagon.t) list = 
    let (set, m1, m2, infl) = SparseOctagon.init (unary, binary, infl) list in
    let (m1, binary, infl) = SparseOctagon.propagate2 (set, m1, m2, infl) in
    let unary = SparseOctagon.propagate1 (m1, binary, infl) in
    (* TODO: evaluate, whether optimize would be a good idea here, or whether propagate1/2 are even necessary*)
    ({unary; binary; infl} : SparseOctagon.t)

  (**
   * process both binary bounds lists to collect the common maximum of both bounds
   * preconditions: 
   * - l1 and l2 ordered wrt. pair order
   * - all implied pair bounds must already have been provided!
  *)
  let cup_list2 l1 l2 = let m2 = SparseOctagon.BinaryMap.empty in
    let infl = SparseOctagon.UnaryMap.empty in
    let rec doit (m2, infl) l1 l2 = match l1, l2 with
      | [], _ | _, [] -> m2, infl
      | (p1, b1)::t1, (p2, b2)::t2 -> 
        (match SparseOctagon.PairLV.compare p1 p2 with (* remove the smaller bounds wrt. pair order until we reach same pairs *)
         | -1 -> doit (m2,infl) t1 l2
         |  0 -> let m2 = SparseOctagon.BinaryMap.add p1 (max b1 b2) m2 in (* collect p1 ≤ b1 ⊔ b2 *)
           let (v1, v2) = p1 in
           let infl = SparseOctagon.add_elem v1 v2 infl in (* make sure to record infl sets *)
           let infl = SparseOctagon.add_elem v2 v1 infl in
           doit (m2, infl) t1 t2
         |  _ -> doit (m2, infl) l1 t2
        ) in
    doit (m2, infl) l1 l2

  (**
   * process both unary bounds lists to collect the common maximum of both bounds
   * preconditions: 
   * - l1 and l2 ordered wrt. literal order
   * - all implied unary bounds must already have been provided!
  *)
  let cup_list l1 l2 = 
    let m1 = SparseOctagon.UnaryMap.empty in        (* initialize with empty unary bounds *)
    let rec doit m1 l1 l2 = match l1, l2 with
      | [], _ | _, [] -> m1
      | (v1, b1) :: t1, (v2, b2) :: t2 -> 
        (match SparseOctagon.LitV.compare v1 v2 with (* remove the smaller bounds wrt. variable order until we reach same variables *)
         | -1 -> doit m1 t1 l2
         |  0 -> let m1 = SparseOctagon.UnaryMap.add v1 (max b1 b2) m1 in (* collect v1 ≤ b1 ⊔ b2 *)
           doit m1 t1 t2
         |  _ -> doit m1 l1 t2
        ) in
    doit m1 l1 l2

  (** enrich binary bounds by summing up unaries *) (* ist jetz oben *)
  (* let complete ({unary; binary; infl} : SparseOctagon.t) = 
    let l1 = SparseOctagon.UnaryMap.bindings unary in (* l1 = list of all unary bounds *)
    let binary, infl = (* cross-product of all unary bounds *)
      List.fold_left (fun (m2, infl) (v1, b1) ->
          List.fold_left (fun (m2, infl) (v2, b2) -> (* ignore same-variable bounds *)
              if      SparseOctagon.LitV.compare v1         v2  = 0 then (m2, infl)
              else if SparseOctagon.LitV.compare v1 (negate v2) = 0 then (m2, infl)
              else
                let p = SparseOctagon.normal (v1, v2) in (* synthesize binary constraints from unary ones *)
                match SparseOctagon.add2_min m2 p (b1 + b2) with  (* collect v1+v2 ≤ b1 + b2 *)
                | None, m2 -> 
                  let infl = SparseOctagon.add_elem v1 v2 infl in
                  let infl = SparseOctagon.add_elem v2 v1 infl in
                  SparseOctagon.check2 m2 p (b1 + b2); (* probably, superfluous! *)
                  m2, infl
                | Some false, m2 -> m2, infl
                | Some true, m2 -> SparseOctagon.check2 m2 p (b1 + b2); (* probably, superfluous! *)
                  m2, infl)
            (m2, infl) l1) 
        (binary, infl) l1 in
    ({unary; binary; infl} : SparseOctagon.t) *)
  

  (** oct1 ⊔ oct2 as convex hull *)
   let cup o1 o2  = (* TODO *)
      (* TODO: was ist mit dingen die implizit gelten? *)
      (* TODO: wozu brauchen wir complete? was ist mit dingen, die implizit gelten? *)
      (* TODO: was ist, wenn sich dinge widersprechen? *)
      let {unary; binary; infl} : SparseOctagon.t = SparseOctagon.strong_closure o1 in  (* full closure on o1 *)
      let {unary = unary2; binary = binary2} : SparseOctagon.t = SparseOctagon.strong_closure o2 in  (* full closure on o2 *)
      (* BinaryMap.bindings is a pair-ordered list *)
      let l1 = SparseOctagon.BinaryMap.bindings binary in
      let l2 = SparseOctagon.BinaryMap.bindings binary2 in 
      let binary, infl = cup_list2 l1 l2 in     (* binary1 ⊔ binary2 *)
      (* UnaryMap.bindings is a literal-ordered list *)
      let l1 = SparseOctagon.UnaryMap.bindings unary in
      let l2 = SparseOctagon.UnaryMap.bindings unary2 in 
      let unary = cup_list l1 l2 in             (*  unary1 ⊔ unary2  *)
      (* TODO: Do we need to think about calling optimize to get rid of redundant pair bounds?*)
      Some ({unary; binary; infl} : SparseOctagon.t)

  (* *************************** *)
  (* fixpoint iteration handling *)
  (* *************************** *)

  let meet octa octb = 
    let oct =
      match octa.d, SparseOctagon.list_of octb.d with
      | None, _ | _, None -> None
      | Some oct, Some l2 -> try Some (cap_list oct l2) (* cap_list ruft propagate2 auf btw, eigentlich wollen wir das doch vermeiden... *)
        with Bot -> None
    in
    { d = oct; env = octb.env }
  
  let join a b = 
    match a.d,b.d with
    | None, _ -> b
    | _, None -> a
    | Some octa, Some octb when (Environment.cmp a.env b.env <> 0)->
      let sup_env = Environment.lce a.env b.env in
      let mod_a = SparseOctagon.dim_add (Environment.dimchange a.env sup_env) octa in
      let mod_b = SparseOctagon.dim_add (Environment.dimchange b.env sup_env) octb in
      {d=cup mod_a mod_b; env = sup_env}
    | Some octa, Some octb -> { d = cup octa octb ; env = a.env} (* same environment, so we can just join the octagons*) 
 
  let leq a b = (* TODO *)
    let env_comp = Environment.cmp a.env b.env in
    if env_comp = -2 || env_comp > 0 then false else
    if is_bot_env a || is_top b then true else
    if is_bot_env b || is_top a then false else
    (* bis hier: macht mann das immer so -> Rückgabewerte in AffineEq anschauen *)
    let oct1, oct2 = Option.get a.d, Option.get b.d in (* octagons rausholen *)
    let oct1'= if env_comp = 0 then oct1 else SparseOctagon.dim_add (Environment.dimchange a.env b.env) oct1 in
    failwith "TODO: SparseOctagonDomain.leq: not implemented"
    (* jetzt haben beide octagons die selben variablennummern, also x hat in beiden z.B. die nummer 1 *)
    (* neuer ansatz:  *)

  let widen a b = failwith "SparseOctagonDomain.widen: not implemented"
  let narrow a b = failwith "SparseOctagonDomain.narrow: not implemented"
  let unify a b = failwith "SparseOctagonDomain.unify: not implemented"

  (* ****************** *)
  (* transfer functions *)
  (* ****************** *)

  (** Remove all bounds that relate to a variable x from oct i.e. [[x := ?]] *)
  let forget_var var oct = let x = Environment.dim_of_var oct.env var in SparseOctagon.forget_var x oct.d

  let forget_vars t vars =
    if is_bot_env t || is_top t then t
    else let newoct = List.fold (fun oct i-> forget_var i t) (t.d) vars in
      { d = newoct; env = t.env }

  let assign_exp ask t var exp _ = failwith "SparseOctagonDomain.assign_exp: not implemented"
  let assign_var t v v' = failwith "SparseOctagonDomain.assign_var: not implemented"
  let assign_var_parallel t vvs = failwith "SparseOctagonDomain.assign_var_parallel: not implemented"
  let assign_var_parallel_with t vvs = failwith "SparseOctagonDomain.assign_var_parallel_with: not implemented"
  let assign_var_parallel' t vvs = failwith "SparseOctagonDomain.assign_var_parallel': not implemented"
  let substitute_exp ask t var exp no_ov = failwith "SparseOctagonDomain.substitute_exp: not implemented"
  let cil_exp_of_lincons1 = Convert.cil_exp_of_lincons1

  (* ***************************** *)
  (* Module AssertionRels demands: *)
  (* ***************************** *)

  let assert_constraint ask d e negate (no_ov: bool Lazy.t) = failwith "SparseOctagonDomain.assert_constraint: not implemented"
  let env t = t.env
  let eval_interval ask = Bounds.bound_texpr
  let invariant t = failwith "SparseOctagonDomain.invariant: not implemented"
  type marshal = t
  (* marshal is not compatible with apron, therefore we don't have to implement it *)
  let marshal t = t
  let unmarshal t = t
  let relift t = t
end

module D2: RelationDomain.RD with type var = Var.t =
struct
  module D = D
  module ConvArg = struct
    let allow_global = false
  end
  include SharedFunctions.AssertionModule (D.V) (D) (ConvArg)
  include D
end