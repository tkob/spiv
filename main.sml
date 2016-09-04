structure Main = struct
  open Parse.Ast
  open LTL

  fun toLTL (FImp (span, f0, f1)) = Imp (toLTL f0, toLTL f1)
    | toLTL (FAnd (span, f0, f1)) = And (toLTL f0, toLTL f1)
    | toLTL (FOr (span, f0, f1)) = Or (toLTL f0, toLTL f1)
    | toLTL (FUntil (span, f0, f1)) = Until (toLTL f0, toLTL f1)
    | toLTL (FRelease (span, f0, f1)) = Release (toLTL f0, toLTL f1)
    | toLTL (FWeakUntil (span, f0, f1)) =WeakUntil (toLTL f0, toLTL f1)
    | toLTL (FNeg (span, f0)) = Neg (toLTL f0)
    | toLTL (FNext (span, f0)) = Next (toLTL f0)
    | toLTL (FFuture (span, f0)) = Future (toLTL f0)
    | toLTL (FGlobal (span, f0)) = Global (toLTL f0)
    | toLTL (FAtom (span, ident)) = Atom ident
    | toLTL (FTop (span)) = Top
    | toLTL (FBottom (span)) = Bottom

  fun main (_, arguments) =
       let
         val fileName = case arguments of [] => NONE | a::_ => SOME a
         val ins = case fileName of
                        NONE => TextIO.stdIn
                      | SOME name => TextIO.openIn name
         fun release () =
               if Option.isSome fileName then TextIO.closeIn ins else ()
       in
         let
           val strm = Lexer.streamifyInstream ins
           val sourcemap = case fileName of
                                NONE => AntlrStreamPos.mkSourcemap ()
                              | SOME n => AntlrStreamPos.mkSourcemap' n
           val trees = Parse.parse sourcemap strm
           val trees = map toLTL trees
           val numParses = length trees
           fun printFormula f = (print (LTL.show f); print "\n")
         in
           print (Int.toString numParses ^ " parse(s)\n");
           List.app printFormula trees;
           release ();
           OS.Process.success
         end
         handle e => (release (); raise e)
       end
end

fun main () =
  let
    val name = CommandLine.name ()
    val arguments = CommandLine.arguments ()
  in
      OS.Process.exit (Main.main (name, arguments))
  end
