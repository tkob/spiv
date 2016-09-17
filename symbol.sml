structure Symbol :> sig
  eqtype t
  val gensym : unit -> t
  val toString : t -> string
end = struct
  type t = int

  local
    val source = ref 0
    fun incr n = n := !n + 1
  in
    fun gensym () = !source before incr source
  end

  val toString = Int.toString
end
