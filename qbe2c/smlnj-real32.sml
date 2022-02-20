(* Dummy implementation for SML/NJ since it doesn't implement Real32. *)

structure Real32 =
struct
  fun toString _ = "42.0"
end

structure PackReal32Little =
struct
  fun fromBytes _ = 42.0
end
