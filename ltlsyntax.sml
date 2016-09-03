structure Token = struct
  datatype token =
    EOF
  | RArrow
  | And
  | Or
  | U
  | R
  | W
  | Not
  | X
  | F
  | G
  | True
  | False
  | LParen
  | RParen
  | Ident of string
  fun show (EOF) = "EOF"
    | show (RArrow) = "RArrow"
    | show (And) = "And"
    | show (Or) = "Or"
    | show (U) = "U"
    | show (R) = "R"
    | show (W) = "W"
    | show (Not) = "Not"
    | show (X) = "X"
    | show (F) = "F"
    | show (G) = "G"
    | show (True) = "True"
    | show (False) = "False"
    | show (LParen) = "LParen"
    | show (RParen) = "RParen"
    | show (Ident a) = "Ident(" ^ a ^ ")"
end
signature Lex = sig
  type strm
  eqtype pos
  type span = pos * pos
  eqtype tok
  val lex : AntlrStreamPos.sourcemap -> strm -> tok * span * strm
  val getPos : strm -> pos
end
functor ParseFun(Lex : Lex where type tok = Token.token and type pos = AntlrStreamPos.pos) = struct
  structure Ast = struct
    datatype formula =
      FImp of Lex.span * formula * formula
    | FAnd of Lex.span * formula * formula
    | FOr of Lex.span * formula * formula
    | FUntil of Lex.span * formula * formula
    | FRelease of Lex.span * formula * formula
    | FWeakUntil of Lex.span * formula * formula
    | FNeg of Lex.span * formula
    | FNext of Lex.span * formula
    | FFuture of Lex.span * formula
    | FGlobal of Lex.span * formula
    | FAtom of Lex.span * string
    | FTop of Lex.span
    | FBottom of Lex.span
    fun showFormula (FImp (span, v0, v1)) =
        "FImp(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FAnd (span, v0, v1)) =
        "FAnd(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FOr (span, v0, v1)) =
        "FOr(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FUntil (span, v0, v1)) =
        "FUntil(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FRelease (span, v0, v1)) =
        "FRelease(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FWeakUntil (span, v0, v1)) =
        "FWeakUntil(" ^ showFormula v0 ^ ", " ^ showFormula v1 ^ ")"
      | showFormula (FNeg (span, v0)) = "FNeg(" ^ showFormula v0 ^ ")"
      | showFormula (FNext (span, v0)) = "FNext(" ^ showFormula v0 ^ ")"
      | showFormula (FFuture (span, v0)) = "FFuture(" ^ showFormula v0 ^ ")"
      | showFormula (FGlobal (span, v0)) = "FGlobal(" ^ showFormula v0 ^ ")"
      | showFormula (FAtom (span, v0)) = "FAtom(" ^ String.toString v0 ^ ")"
      | showFormula (FTop (span)) = "FTop(" ^ ")"
      | showFormula (FBottom (span)) = "FBottom(" ^ ")"
  end
  structure Category = struct
    datatype category =
      EOF
    | RArrow
    | And
    | Or
    | U
    | R
    | W
    | Not
    | X
    | F
    | G
    | True
    | False
    | LParen
    | RParen
    | Ident of string
    | Formula of Ast.formula
    | Formula1 of Ast.formula
    | Formula2 of Ast.formula
    | Formula3 of Ast.formula
    fun show (EOF) = "EOF"
      | show (RArrow) = "RArrow"
      | show (And) = "And"
      | show (Or) = "Or"
      | show (U) = "U"
      | show (R) = "R"
      | show (W) = "W"
      | show (Not) = "Not"
      | show (X) = "X"
      | show (F) = "F"
      | show (G) = "G"
      | show (True) = "True"
      | show (False) = "False"
      | show (LParen) = "LParen"
      | show (RParen) = "RParen"
      | show (Ident a) = "Ident(" ^ a ^ ")"
      | show (Formula a) = "Formula(" ^ Ast.showFormula a ^ ")"
      | show (Formula1 a) = "Formula1(" ^ Ast.showFormula a ^ ")"
      | show (Formula2 a) = "Formula2(" ^ Ast.showFormula a ^ ")"
      | show (Formula3 a) = "Formula3(" ^ Ast.showFormula a ^ ")"
    fun fromToken (Token.EOF) = EOF
      | fromToken (Token.RArrow) = RArrow
      | fromToken (Token.And) = And
      | fromToken (Token.Or) = Or
      | fromToken (Token.U) = U
      | fromToken (Token.R) = R
      | fromToken (Token.W) = W
      | fromToken (Token.Not) = Not
      | fromToken (Token.X) = X
      | fromToken (Token.F) = F
      | fromToken (Token.G) = G
      | fromToken (Token.True) = True
      | fromToken (Token.False) = False
      | fromToken (Token.LParen) = LParen
      | fromToken (Token.RParen) = RParen
      | fromToken (Token.Ident a) = Ident a
  end
  open Category
  exception Parse of category * Lex.pos * int
  fun go stateNumber stack category span =
      case stateNumber of
        30 => st30 stack category span
      | 24 => st24 stack category span
      | 19 => st19 stack category span
      | 18 => st18 stack category span
      | 17 => st17 stack category span
      | 16 => st16 stack category span
      | 15 => st15 stack category span
      | 14 => st14 stack category span
      | 13 => st13 stack category span
      | 12 => st12 stack category span
      | 8 => st8 stack category span
      | 7 => st7 stack category span
      | 6 => st6 stack category span
      | 5 => st5 stack category span
      | 3 => st3 stack category span
      | 1 => st1 stack category span
      | 0 => st0 stack category span
      | _ => []
  and st31r0 ((RParen, pos2, stNum2)::(Formula sv1, pos1, stNum1)::(LParen, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (sv1)) (pos0, pos)
    | st31r0 stack pos = []
  and st30 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 30)
      in
        case category of
          RArrow => [(13, (stackItem::stack))]
        | RParen => [] @ List.concat [st31r0 (stackItem::stack) toPos]
        | c => [] (* raise Parse (c, pos, 30) *)
      end
  and st29r0 ((Formula3 sv1, pos1, stNum1)::(G, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FGlobal ((pos0, pos), sv1))) (pos0, pos)
    | st29r0 stack pos = []
  and st28r0 ((Formula3 sv1, pos1, stNum1)::(F, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FFuture ((pos0, pos), sv1))) (pos0, pos)
    | st28r0 stack pos = []
  and st27r0 ((Formula3 sv1, pos1, stNum1)::(X, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FNext ((pos0, pos), sv1))) (pos0, pos)
    | st27r0 stack pos = []
  and st26r0 ((Formula3 sv1, pos1, stNum1)::(Not, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FNeg ((pos0, pos), sv1))) (pos0, pos)
    | st26r0 stack pos = []
  and st25r0 ((Formula2 sv2, pos2, stNum2)::(And, pos1, stNum1)::(Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula1 (Ast.FAnd ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st25r0 stack pos = []
  and st25r1 ((Formula2 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula1 (sv0)) (pos0, pos)
    | st25r1 stack pos = []
  and st24 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 24)
      in
        case category of
          W => [(15, (stackItem::stack))]
        | R => [(16, (stackItem::stack))]
        | Or => [(18, (stackItem::stack))]
        | And => [(19, (stackItem::stack))]
        | U => [(17, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 24) *)
      end
  and st23r0 ((Formula2 sv2, pos2, stNum2)::(Or, pos1, stNum1)::(Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula1 (Ast.FOr ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st23r0 stack pos = []
  and st23r1 ((Formula2 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula1 (sv0)) (pos0, pos)
    | st23r1 stack pos = []
  and st22r0 ((Formula3 sv2, pos2, stNum2)::(U, pos1, stNum1)::(Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula2 (Ast.FUntil ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st22r0 stack pos = []
  and st21r0 ((Formula3 sv2, pos2, stNum2)::(R, pos1, stNum1)::(Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula2 (Ast.FRelease ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st21r0 stack pos = []
  and st20r0 ((Formula3 sv2, pos2, stNum2)::(W, pos1, stNum1)::(Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula2 (Ast.FWeakUntil ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st20r0 stack pos = []
  and st19 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 19)
      in
        case category of
          Formula2 _ => [] @ List.concat [st25r0 (stackItem::stack) toPos, st25r1 (stackItem::stack) toPos]
        | Formula1 _ => [(24, (stackItem::stack))]
        | Formula3 _ => [] @ List.concat [st4r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 19) *)
      end
  and st18 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 18)
      in
        case category of
          Formula2 _ => [] @ List.concat [st23r0 (stackItem::stack) toPos, st23r1 (stackItem::stack) toPos]
        | Formula1 _ => [(24, (stackItem::stack))]
        | Formula3 _ => [] @ List.concat [st4r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 18) *)
      end
  and st17 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 17)
      in
        case category of
          Formula3 _ => [] @ List.concat [st22r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 17) *)
      end
  and st16 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 16)
      in
        case category of
          Formula3 _ => [] @ List.concat [st21r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 16) *)
      end
  and st15 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 15)
      in
        case category of
          Formula3 _ => [] @ List.concat [st20r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 15) *)
      end
  and st14 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 14)
      in
        case category of
          W => [(15, (stackItem::stack))]
        | R => [(16, (stackItem::stack))]
        | U => [(17, (stackItem::stack))]
        | Or => [(18, (stackItem::stack))]
        | And => [(19, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 14) *)
      end
  and st14r0 ((Formula1 sv2, pos2, stNum2)::(RArrow, pos1, stNum1)::(Formula sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula (Ast.FImp ((pos0, pos), sv0, sv2))) (pos0, pos)
    | st14r0 stack pos = []
  and st13 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 13)
      in
        case category of
          Formula2 _ => [] @ List.concat [st2r0 (stackItem::stack) toPos]
        | Formula1 _ => [(14, (stackItem::stack))] @ List.concat [st14r0 (stackItem::stack) toPos]
        | Formula3 _ => [] @ List.concat [st4r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 13) *)
      end
  and st12 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 12)
      in
        case category of
          Formula _ => [(30, (stackItem::stack))]
        | Formula2 _ => [] @ List.concat [st2r0 (stackItem::stack) toPos]
        | Formula1 _ => [(3, (stackItem::stack))] @ List.concat [st3r0 (stackItem::stack) toPos]
        | Formula3 _ => [] @ List.concat [st4r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 12) *)
      end
  and st11r0 ((False, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FBottom ((pos0, pos)))) (pos0, pos)
    | st11r0 stack pos = []
  and st10r0 ((True, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FTop ((pos0, pos)))) (pos0, pos)
    | st10r0 stack pos = []
  and st9r0 ((Ident sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula3 (Ast.FAtom ((pos0, pos), sv0))) (pos0, pos)
    | st9r0 stack pos = []
  and st8 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 8)
      in
        case category of
          Formula3 _ => [] @ List.concat [st29r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 8) *)
      end
  and st7 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 7)
      in
        case category of
          Formula3 _ => [] @ List.concat [st28r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 7) *)
      end
  and st6 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 6)
      in
        case category of
          Formula3 _ => [] @ List.concat [st27r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 6) *)
      end
  and st5 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 5)
      in
        case category of
          Formula3 _ => [] @ List.concat [st26r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 5) *)
      end
  and st4r0 ((Formula3 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula2 (sv0)) (pos0, pos)
    | st4r0 stack pos = []
  and st3 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 3)
      in
        case category of
          W => [(15, (stackItem::stack))]
        | R => [(16, (stackItem::stack))]
        | U => [(17, (stackItem::stack))]
        | Or => [(18, (stackItem::stack))]
        | And => [(19, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 3) *)
      end
  and st3r0 ((Formula1 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula (sv0)) (pos0, pos)
    | st3r0 stack pos = []
  and st2r0 ((Formula2 sv0, pos0, stNum0)::stack) pos =
      go stNum0 stack (Formula1 (sv0)) (pos0, pos)
    | st2r0 stack pos = []
  and st1 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 1)
      in
        case category of
          RArrow => [(13, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 1) *)
      end
  and st1r0 stack pos = [(~1, stack)]
  and st0 stack category (fromPos, toPos) =
      let
        val stackItem = (category, fromPos, 0)
      in
        case category of
          Formula _ => [(1, (stackItem::stack))] @ List.concat [st1r0 (stackItem::stack) toPos]
        | Formula2 _ => [] @ List.concat [st2r0 (stackItem::stack) toPos]
        | Formula1 _ => [(3, (stackItem::stack))] @ List.concat [st3r0 (stackItem::stack) toPos]
        | Formula3 _ => [] @ List.concat [st4r0 (stackItem::stack) toPos]
        | Not => [(5, (stackItem::stack))]
        | X => [(6, (stackItem::stack))]
        | F => [(7, (stackItem::stack))]
        | G => [(8, (stackItem::stack))]
        | Ident _ => [] @ List.concat [st9r0 (stackItem::stack) toPos]
        | True => [] @ List.concat [st10r0 (stackItem::stack) toPos]
        | False => [] @ List.concat [st11r0 (stackItem::stack) toPos]
        | LParen => [(12, (stackItem::stack))]
        | c => [] (* raise Parse (c, pos, 0) *)
      end
  fun parse sourcemap strm =
      let
        val pos = Lex.getPos strm
        val stacks = [(0, [])]
        fun loop stacks strm =
            let
              val pos = Lex.getPos strm
              val (token, span, strm') = Lex.lex sourcemap strm
            in
              case token of
                Token.EOF =>
                let
                  val completeStacks = List.filter (fn (st, _) => st = ~1) stacks
                  val topCategories = map (fn (st, stack) => hd stack) completeStacks
                  fun toAst (Formula sv, _, _) = SOME sv | toAst _ = NONE
                in
                  List.mapPartial toAst topCategories
                end
              | _ =>
                let
                  val category = Category.fromToken token
                  val stacks' = List.concat (map (fn (st, stack) => go st stack category span) stacks)
                in
                  loop stacks' strm'
                end
            end
      in
        loop stacks strm
      end
end
