structure LTL = struct
  datatype formula =
    Imp of formula * formula
  | And of formula * formula
  | Or of formula * formula
  | Until of formula * formula
  | Release of formula * formula
  | WeakUntil of formula * formula
  | Neg of formula
  | Next of formula
  | Future of formula
  | Global of formula
  | Atom of string
  | Top
  | Bottom

  fun negate (Neg f) = f
    | negate f = Neg f

  fun show (Imp (f0, f1)) =
      "(" ^ show f0 ^ " -> " ^ show f1 ^ ")"
    | show (And (f0, f1)) =
      "(" ^ show f0 ^ " & " ^ show f1 ^ ")"
    | show (Or (f0, f1)) =
      "(" ^ show f0 ^ " | " ^ show f1 ^ ")"
    | show (Until (f0, f1)) =
      "(" ^ show f0 ^ " U " ^ show f1 ^ ")"
    | show (Release (f0, f1)) =
      "(" ^ show f0 ^ " R " ^ show f1 ^ ")"
    | show (WeakUntil (f0, f1)) =
      "(" ^ show f0 ^ " W " ^ show f1 ^ ")"
    | show (Neg f) = "(!" ^ show f ^ ")"
    | show (Next f) = "(X " ^ show f ^ ")"
    | show (Future f) = "(F " ^ show f ^ ")"
    | show (Global f) = "(G " ^ show f ^ ")"
    | show (Atom ident) = ident
    | show Top = "true"
    | show Bottom = "false"
end
