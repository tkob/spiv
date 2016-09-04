structure LTLConv = struct
  open Parse.Ast

  fun simplify (FImp   (span, f1, f2)) = FImp   (span, simplify f1, simplify f2)
    | simplify (FAnd   (span, f1, f2)) = FAnd   (span, simplify f1, simplify f2)
    | simplify (FOr    (span, f1, f2)) = FOr    (span, simplify f1, simplify f2)
    | simplify (FUntil (span, f1, f2)) = FUntil (span, simplify f1, simplify f2)
    | simplify (FRelease (span, f1, f2)) =
        let
          val f1' = simplify f1
          val f2' = simplify f2
        in
          (* p R q = ~(~p U ~q) *)
          FNeg (span, FUntil (span, FNeg (span, f1'), FNeg (span, f2')))
        end
    | simplify (FWeakUntil (span, f1, f2)) =
        let
          val f1' = simplify f1
          val f2' = simplify f2
        in
          (* p W q = p U q | G p *)
          FOr (span, FUntil (span, f1', f2'), simplify (FGlobal (span, f1')))
        end
    | simplify (FNeg  (span, f)) = FNeg  (span, simplify f)
    | simplify (FNext (span, f)) = FNext (span, simplify f)
    | simplify (FFuture (span, f)) =
        (* F p = true until p *)
        FUntil (span, FTop span, simplify f)
    | simplify (FGlobal (span, f)) =
        (* G p = false release p = ~(true U ~p)
           ``It is not the case that sometime p does not hold'' *)
        FNeg (span, FUntil (span, FTop span, FNeg(span, f)))
    | simplify (FAtom (span, ident)) = FAtom (span, ident)
    | simplify (FTop (span)) = FTop span
    | simplify (FBottom (span)) = FBottom span

  infix ==
  fun (FImp (_, f1, f2) == FImp (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FImp (_, f1, f2) == _) = false
    | (FAnd (_, f1, f2) == FAnd (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FAnd (_, f1, f2) == _) = false
    | (FOr (_, f1, f2) == FOr (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FOr (_, f1, f2) == _) = false
    | (FUntil (_, f1, f2) == FUntil (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FUntil (_, f1, f2) == _) = false
    | (FRelease (_, f1, f2) == FRelease (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FRelease (_, f1, f2) == _) = false
    | (FWeakUntil (_, f1, f2) == FWeakUntil (_, g1, g2)) = f1 == g1 andalso f2 == g2
    | (FWeakUntil (_, f1, f2) == _) = false
    | (FNeg (_, f) == FNeg (_, g)) = f == g
    | (FNeg (_, f) == _) = false
    | (FNext (_, f) == FNext (_, g)) = f == g
    | (FNext (_, f) == _) = false
    | (FFuture (_, f) == FFuture (_, g)) = f == g
    | (FFuture (_, f) == _) = false
    | (FGlobal (_, f) == FGlobal (_, g)) = f == g
    | (FGlobal (_, f) == _) = false
    | (FAtom (_, f) == FAtom (_, g)) = f = g
    | (FAtom (_, f) == _) = false
    | (FTop (_) == FTop (_)) = true
    | (FTop (_) == _) = false
    | (FBottom (_) == FBottom (_)) = true
    | (FBottom (_) == _) = false

  fun mem (x, []) = false
    | mem (x, y::ys) = if x == y then true else mem (x, ys)
  fun union ([], ys) = ys
    | union (x::xs, ys) = if mem (x, ys) then ys else union (xs, x::ys)
end
