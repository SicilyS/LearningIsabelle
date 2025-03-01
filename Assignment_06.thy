theory Assignment_06
  imports Main
begin

datatype aexp = Const | Var string |Plus aexp aexp

fun aval :: "aexp => state => val" where


definition null_state ("<>") where
  "null_state \<equiv>  \<lambda>x. 0"

end