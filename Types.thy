theory Types
imports Main
begin

value "True"
value "False"
value "False \<or> True"

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conj True True = True"
| "conj _  	_  = False"
(*underscore is wildcard. evaluates top case down*)

value "1 :: nat"
value "(1 :: nat) + 10"
(*assigning type to one element makes it assume for all. 10 is assumed to be nat*)

(*suc is for succession

datatype nat = 0 | Suc nat

1 := Suc 0
2 := Suc Suc 0

^how natural numbers are defined. then labeled as 1 2 etc
*)

value "0 :: nat"
value "Suc 0"
value "Suc (Suc 0)"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "add 0       b = b"
| "add (Suc a) b = Suc (add a b)"

(*defined recursively^ we know its total because it approaches a smaller number with each iteration*)

lemma add_02 [simp]: "add a 0 = a"
  apply (induction a)
   apply (auto)
  done

(*[simp] adds the lemma to tools it will use in auto. will now work in auto*)

lemma "add a b =add b a"
  apply (induction a)
   apply (auto)



end
