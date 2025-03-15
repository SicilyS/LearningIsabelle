theory Options
  imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val" 


datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x ) s stk = s(x ) # stk" |
"exec1 ADD _ (j # i # stk) = (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x ) = [LOAD x ]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"


lemma "exec (comp a) s stk = aval a s # stk "
  apply (induction a)

lemma exec_append: ""

(*exercise 3.10*)

(*need to define hd2 and tl2*)
fun exec1' :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1' (LOADI n) _ stk = Some (n # stk)"
| "exec1' (LOADI x) s stk = Some ((s x) # stk)"
| "exec1' ADD _ [] = None"
| "exec1' ADD _ [_] = None"
| "exec1' ADD _ stk = Some ((hd2 stk + hd stk) # tl2 stk)"


fun exec' :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec' [] _ stk = Some stk" |
"exec' (i#is) s stk = (case (exec1 i s stk) of
                        None \<Rightarrow> None
                      | Some new_stk \<Rightarrow> exec' is s new_stk)"

lemma exec'_append: "exec' is1 s stk = Some new_stk \<Longrightarrow> exec' (is1 @ is2) s stk = exec' is2 s new_stk"
  apply (induction is1 arbitrary: stk)
  apply(auto split: option.split)
  done

lemma "exec' (comp a) s stk = Some (aval a s # stk)"
  apply (induction a arbitrary: stk)
  by (auto simp add: exec'_append)

end