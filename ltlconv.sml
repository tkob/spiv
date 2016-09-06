structure LTLConv = struct
  open LTL

  fun simplify (Imp   (f1, f2)) = Imp   (simplify f1, simplify f2)
    | simplify (And   (f1, f2)) = And   (simplify f1, simplify f2)
    | simplify (Or    (f1, f2)) = Or    (simplify f1, simplify f2)
    | simplify (Until (f1, f2)) = Until (simplify f1, simplify f2)
    | simplify (Release (f1, f2)) =
        let
          val f1' = simplify f1
          val f2' = simplify f2
        in
          (* p R q = ~(~p U ~q) *)
          Neg (Until (Neg (f1'), Neg (f2')))
        end
    | simplify (WeakUntil (f1, f2)) =
        let
          val f1' = simplify f1
          val f2' = simplify f2
        in
          (* p W q = p U q | G p *)
          Or (Until (f1', f2'), simplify (Global (f1')))
        end
    | simplify (Neg  (f)) = Neg  (simplify f)
    | simplify (Next (f)) = Next (simplify f)
    | simplify (Future (f)) =
        (*  p = true until p *)
        Until (Top, simplify f)
    | simplify (Global (f)) =
        (* G p = false release p = ~(true U ~p)
           ``It is not the case that sometime p does not hold'' *)
        Neg (Until (Top, Neg(f)))
    | simplify (Atom (ident)) = Atom (ident)
    | simplify Top = Top
    | simplify Bottom = Bottom

  fun mem (x, []) = false
    | mem (x, y::ys) = if x = y then true else mem (x, ys)
  fun union ([], ys) = ys
    | union (x::xs, ys) = if mem (x, ys) then ys else union (xs, x::ys)
  (* 'a list -> 'a list list *)
  fun powerSets [] = [[]]
    | powerSets [x] = [[x], []]
    | powerSets (x::xs) =
        let
          val powerSets' = powerSets xs
          fun addX xs = x::xs
          val powerSets'' = map addX powerSets'
        in
          powerSets'' @ powerSets'
        end
  fun isSubset (xs, ys) =
        List.all (fn x => mem (x, ys)) xs
  fun maximal (xs, yss) =
        let
          fun pred ys = not (isSubset (xs, ys)) orelse xs = ys
        in
          List.all pred yss
        end

  (* formula -> formula list *)
  fun closure (g as Imp (f1, f2)) =
        g::Neg (g)::(union (closure f1, closure f2))
    | closure (g as And (f1, f2)) =
        g::Neg (g)::(union (closure f1, closure f2))
    | closure (g as Or (f1, f2)) =
        g::Neg (g)::(union (closure f1, closure f2))
    | closure (g as Until (f1, f2)) =
        g::Neg (g)::(union (closure f1, closure f2))
    | closure (g as Next (f)) =
        g::Neg (g)::closure f
    | closure (Neg (f)) = closure f
    | closure (atom as Atom (_)) = [atom, Neg (atom)]
    | closure Top = [Top, Bottom]
    | closure Bottom = [Top, Bottom]
    | closure f = raise Fail ("unsimplified formula: " ^ LTL.show f)

  (* formula list -> formula list list *)
  fun subsets closure =
        let
          fun nonNegated (Neg _) = false
            | nonNegated _ = true
          val powerSets = powerSets closure
          fun consistent fs =
                let
                  fun containsFormulaOrComplementButNotBoth f =
                        let
                          val a = mem (f, fs)
                          val b = mem (negate f, fs)
                        in
                          (a orelse b) andalso not (a andalso b)
                        end
                  fun consistentAboutBoolean (f as Imp (f1, f2)) =
                        let
                          val a = mem (f, fs)
                          val b = not (mem (f1, fs)) orelse mem (f2, fs)
                        in
                          (not a orelse b) andalso (not b orelse a)
                        end
                    | consistentAboutBoolean (f as And (f1, f2)) =
                        let
                          val a = mem (f, fs)
                          val b = mem (f1, fs) andalso mem (f2, fs)
                        in
                          (not a orelse b) andalso (not b orelse a)
                        end
                    | consistentAboutBoolean (f as Or (f1, f2) )=
                        let
                          val a = mem (f, fs)
                          val b = mem (f1, fs) orelse mem (f2, fs)
                        in
                          (not a orelse b) andalso (not b orelse a)
                        end
                    | consistentAboutBoolean _ = true
                  fun consistentAboutUntil (Until (f1, f2)) =
                        mem (f1, fs) orelse mem (f2, fs)
                    | consistentAboutUntil (Neg (Until (f1, f2))) =
                        mem (negate f2, fs)
                    | consistentAboutUntil _ = true
                in
                  List.all
                    containsFormulaOrComplementButNotBoth
                    (List.filter nonNegated closure)
                  andalso
                  List.all consistentAboutBoolean closure
                  andalso
                  List.all consistentAboutUntil fs
                end
        in
          List.filter consistent powerSets
        end

  (* 'a list -> ('a * 'a) list *)
  fun allPairs xs =
        let
          fun pairOf a b = (a, b)
          fun flatMap f l = List.concat (map f l)
        in
          flatMap (fn x => map (pairOf x) xs) xs
        end
end
