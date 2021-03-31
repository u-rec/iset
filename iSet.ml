(* review: Kacper Jabłoński *)

(* od do *)
type pair = int * int

(* lewe poddrzewo, przedział w danym wierzchołku,
 * prawe poddrzewo, wysokość, szerokość przedziału w poddrzewie
 * zbudowane drzewo jest drzewem AVL o maksymalnej różnicy wysokości 2*)
type t =
  | Empty
  | Node of t * pair * t * int * int

let empty = Empty

let is_empty set =
  set = Empty

let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0

(* szerokość przedziału w drzewie *)
let width = function
  | Node (_, _, _, _, w) -> w
  | Empty -> 0

(* oblicza szerokosc dla korzenia k, z przylaczonymi wierzcholkami l, r *)
let width_calculate l k r =
  let k1 = fst k in
  let k2 = snd k
  in
  if l + r < 0 then max_int
  else if k2 - k1 + 1 <= 0 then max_int
  else if l + r - k1 + k2 + 1 <= 0 then max_int
  else l + r + k2 - k1 + 1

(*bezpośrednio tworzy drzewo z 2 poddrzew i korzenia, zakłada, że
poddrzewa są zbalansowane, również między sobą*)
let make l k r =
  let hl = height l in
  let hr = height r in
  let wl = width l in
  let wr = width r in
  Node (l, k, r, max hl hr + 1, width_calculate wl k wr)

(*balansuje poddrzewo o synach l i r, korzeniu k*)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r

(*zwraca najmniejszy element drzewa*)
let rec min_element = function
  | Empty -> assert false
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_element l

(*zwraca drzewo bez najmniejszego elementu*)
let rec rmv_min = function
  | Empty -> assert false
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (rmv_min l) k r

(*odejmowanie 2 liczb dodatnich z uwzględnieniem ograniczeń zakresu int*)
let minus a b =
  if a - b > a then min_int else a - b

(*jw., dodawanie*)
let plus a b =
  if a + b < a then max_int else a + b

(*zwraca zbalansowane drzewo z usuniętymi wszystkimi przedziałami mającymi
  część wspólną z x, oraz teoriomnogościową sumę usuniętych elementów i x *)
let rec delete_intersect x w = function
  | Empty -> (Empty, x)
  | Node (l, k, r, _, _) ->
    if snd x < minus (fst k) 1 then
      let res = delete_intersect x w l in
      ((bal (fst res) k r), snd res)
    else if plus (snd k) 1 < fst x then
      let res = delete_intersect x w r in
      ((bal l k (fst res)), snd res)
    else
      let p = (min (fst x) (fst k), max (snd x) (snd k)) in
      if w = (-1) then
        delete_intersect p w l
      else if w = 1 then
        delete_intersect p w r
      else
        let (ltree, lint) = delete_intersect p (-1) l in
        let (rtree, rint) = delete_intersect p 1 r in
        let res = (min (fst lint) (fst rint), max (snd lint) (snd rint)) in
        if ltree = Empty then (rtree, res)
        else if rtree = Empty then (ltree, res)
        else (bal ltree (min_element rtree) (rmv_min rtree), res)

(*dodaje przedział xin do drzewa tree*)
let add xin tree =
  let aux = delete_intersect xin 0 tree in
  let rec add_aux x = function
    | Empty -> make Empty x Empty
    | Node (l, k, r, _, _) ->
        if fst x < fst k then
          bal (add_aux x l) k r
        else
          bal l k (add_aux x r) in
  add_aux (snd aux) (fst aux)

(*usuwa przedział x z drzewa tree*)
let remove x tree =
  let aux = delete_intersect x 0 tree in
  if fst x > fst (snd aux) then
    if snd x < snd (snd aux) then
      add (fst (snd aux), fst x - 1) (add (snd x + 1, snd (snd aux)) (fst aux))
    else add (fst (snd aux), fst x - 1) (fst aux)
  else
    if snd x < snd (snd aux) then
      add (snd x + 1, snd (snd aux)) (fst aux)
    else fst aux

(*sprawdza czy element x występuje w drzewie*)
let rec mem x = function
  | Empty -> false
  | Node (l, k, r, _, _) ->
    if x >= fst k && x <= snd k then true
    else if x < fst k then mem x l
    else mem x r

(*iteruje po wszystkich wierzchołkach drzewa*)
let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r in
  loop set

(*fold po wszystkich wierzchołkach drzewa*)
let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

(*zwraca tablicę wszystkich wierzchołków drzewa*)
let elements set =
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
  loop [] set

(*ile elementów mniejszych od x*)
let rec below x = function
  | Empty -> 0
  | Node (l, k, r, _, _) ->
    if x >= fst k && x <= snd k then
      width_calculate (width l) (fst k, x) 0
    else if x < fst k then below x l
    else width_calculate (width l) k (below x r)

(*dzieli drzewo na 2 poddrzewa i bool*)
let split x tree =
  (remove (x, max_int) tree, mem x tree, remove (min_int, x) tree)
