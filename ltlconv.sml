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
end
