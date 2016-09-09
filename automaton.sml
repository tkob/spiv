structure Automaton = struct
  type ''a automaton = { states : ''a list, transitions : (''a * ''a) list }

  fun printDot showState (automaton : ''a automaton) =
        let
          val count = ref 1
          fun gensym () = "q" ^ Int.toString (!count) before count := !count + 1
          val states = #states automaton
          val transitions = #transitions automaton
          val namesAndStates = map (fn state => (gensym (), state)) states
          fun lookupName (state, []) = raise Fail ""
            | lookupName (state, (name, state')::namesAndStates) =
                if state = state' then name
                else lookupName (state, namesAndStates)
          fun printLabel state = (
                print (lookupName (state, namesAndStates));
                print " [label = \"";
                print (showState state);
                print "\"];\n";
                ())
          fun printTransition (q1, q2) = (
                print (lookupName (q1, namesAndStates));
                print " -> ";
                print (lookupName (q2, namesAndStates));
                print ";\n";
                ())
        in
          print "digraph automaton {\n";
          List.app printLabel states;
          List.app printTransition transitions;
          print "}\n";
          ()
        end
end
