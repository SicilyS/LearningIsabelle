theory Assignment_08
  imports Big_Step
begin

(*
commented out because com is defined in an import
datatype com = SKIP
  | Assign vname aexp
  | Seq com com
  | If bexp com com
  | While bexp com
*)

(*exercise 7.1*)

fun assigned :: "com \<Rightarrow> vname set" where
  "assigned SKIP = {}"
| "assigned (Assign x a) = {x}"
| "assigned (Seq c1 c2) = assigned c1 \<union> assigned c2"
| "assigned (If b1 c1 c2) = assigned c1  \<union> assigned c2"
| "assigned (While b1 c1) = assigned c1 "

value "assigned (Seq (Assign ''x'' (Plus (V ''t'') (N 3) ) )  (Seq (Assign ''y'' (N 5)) (Assign ''n'' (V ''z'')) ) )"
value "assigned (Seq (Assign ''x'' (Plus (N 3)(N 3)))  ((Assign ''y'' (V ''z''))) )"


lemma "\<lbrakk> (c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow>  s x = t x" 
  apply (induction rule: big_step_induct)
        apply (auto)
  done
  

(*exercise 7.2*)
(*REDO PROPERLY. account for SEQ(SKIP)(SKIP)*)
fun skip :: "com \<Rightarrow> bool" where
  "skip SKIP = True"
| "skip (Seq c1 c2) = (skip c1 \<and> skip c2)"
| "skip (If b1 c1 c2) = (skip c1 \<and> skip c2)"
| "skip (While b1 c1) = skip c1"
| "skip (Assign x1 a1) = False"

value "skip (Seq SKIP SKIP)"
value "(skip SKIP \<and> skip SKIP)"

lemma [simp]: "skip (x1 ::= x2) \<Longrightarrow> x1 ::= x2 \<sim> SKIP"
  by auto

lemma [simp]: "c1 \<sim> SKIP \<Longrightarrow> c2 \<sim> SKIP \<Longrightarrow> c1;; c2 \<sim> SKIP"
  by (metis Seq Skip big_step_determ)

lemma [simp]: "c1 \<sim> SKIP \<Longrightarrow> c2 \<sim> SKIP \<Longrightarrow> IF b THEN c1 ELSE c2 \<sim> SKIP"
  by blast

lemma [simp]: "c \<sim> SKIP \<Longrightarrow>  WHILE x1 DO c \<sim> SKIP"
  try0


lemma "skip c \<Longrightarrow> c \<sim> SKIP"
  apply(induction c)
      apply (simp)+
  sorry

(*exercise 7.3*)

fun deskip :: "com \<Rightarrow> com" where
  "deskip (Assign x a) = Assign x a"
| "deskip SKIP = SKIP"
| "deskip (Seq c1 c2) = (case (deskip c1, deskip c2) of
    (SKIP, c2') \<Rightarrow> c2'
  | (c1', SKIP) \<Rightarrow> c1'
  | (c1', c2' ) \<Rightarrow> (c1';; c2'))"
| "deskip (If b c1 c2) = (case( deskip c1, deskip c2) of
    (SKIP, SKIP) \<Rightarrow> SKIP
  | (c1', c2' ) \<Rightarrow> (IF b THEN c1' ElSE c2' ))"
| "deskip (While b1 c1) = (case(deskip c1, deskip c2) of
    SKIP \<Rightarrow> SKIP
  | c1' \<Rightarrow> WHILE b DO c')"


value "deskip (SKIP;; WHILE b DO (x ::= a;; SKIP))"

(*Bottom up vs Top down problem. use cases in def*)
value "deskip ( WHILE b DO WHILE b DO SKIP)"


(*currently not required for assignment*)
lemma "deskip c \<sim> c"
  apply(induction c rule: deskip.induct)
  apply(simp)
  apply (auto)
  sorry
(*exercise 7.4*)

inductive astep:: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool"(infix "\<leadsto>" 50) where
  Assignment: "(V x, s) \<leadsto> N (s x)"
| Plus_Constant: "(Plus (N i)(N j), s) \<leadsto> N (i + j)"
| Plus_Left: "(a1, s) \<leadsto> (N i) \<Longrightarrow> (Plus a1 a2, s) \<leadsto> Plus (N i) a2 "
| Plus_Right: "(a2, s) \<leadsto> (N j) \<Longrightarrow> (Plus (N i) a2, s) \<leadsto> Plus (N i) (N j)"

lemmas astep_induct = astep.induct [split_format (complete)]

(*BELOW WORKS AS WELL

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
  apply (induction rule: astep.induct [split_format (complete)])
     apply (auto)
  done
*)


lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
  fix x s
  show " aval (V x) s = aval (N (s x)) s" by simp
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by simp
next
  fix a1 a2 s i
  assume "(a1, s) \<leadsto> N i" " aval a1 s = aval (N i) s"
  show "aval (Plus a1 a2) s = aval (Plus (N i) a2) s" using \<open>aval a1 s = aval (N i) s\<close> by auto
next
  fix a2 s j i
  assume "(a2, s) \<leadsto> N j""aval a2 s = aval (N j) s"
  show "aval (Plus (N i) a2) s = aval (Plus (N i) (N j)) s " 
    by (simp add: \<open>aval a2 s = aval (N j) s\<close>)
  




end