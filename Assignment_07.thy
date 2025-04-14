theory Assignment_07
  imports Main
begin


(* exercise 3.3 *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val" 


definition null_state ("<>") where
  "null_state \<equiv>  \<lambda>x. 0"


fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" 
| "aval (V x ) s = s x" 
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (V '' x '')) (\<lambda>x . 0)"


fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" 
| "asimp_const (V x) = V x"
| "asimp_const  (Plus a1 a2) = (case (asimp_const a1, asimp_const a2) of (N n1, N n2) \<Rightarrow> N(n1 + n2)
  | (b1, b2) \<Rightarrow> Plus b1 b2)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)"
| "plus (N i) a  = (if i=0 then a else Plus (N i) a)"
| "plus a (N i) = (if i=0 then a else Plus a (N i))"
| "plus a1 a2 = Plus a1 a2"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"


(*exercise 3.7*)

(* boolean constants, negation, conjunction and comparison of expressions for less-than*)
datatype bexp= Bc bool | Not bexp | And bexp bexp | Less aexp aexp


fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v"
| "bval (Not b) s = (\<not> bval b s)"
| "bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"
| "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"


fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True) = Bc False"
| "not (Bc False) = Bc True"
| "not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b"
| "and b (Bc True) = b"
| "and (Bc False) b = Bc False"
| "and b (Bc False) = Bc False"
| "and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n1) (N n2) = Bc(n1 < n2)"
| "less a1 a2  = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v"
| "bsimp (Not b) = not(bsimp b)" 
| "bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" 
| "bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"


(*exercise 3.9*)

datatype pbexp =
VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR x ) s = s x"
| "pbval (NEG b) s = (\<not> pbval b s)" 
| "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" 
| "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"


fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR x) = True"
| "is_nnf (NEG (VAR x)) = True"
| "is_nnf (NEG _) = False"
| "is_nnf (AND b1 b2) = ((is_nnf b1)\<and> (is_nnf b2))"
| "is_nnf (OR b1 b2) = ((is_nnf b1) \<and> (is_nnf b2))"

value "is_nnf (VAR ''x'')"


fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = VAR x"
| "nnf (NEG (VAR x)) = (NEG (VAR x))"
| "nnf (NEG (NEG (b1))) = nnf b1"
| "nnf (AND b1 b2) = AND (nnf b1) (nnf b2)"
| "nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"
| "nnf (NEG (AND b1 b2)) = OR (nnf (NEG b1)) (nnf (NEG b2))"
| "nnf (NEG (OR b1 b2)) = AND (nnf (NEG b1)) (nnf (NEG b2))"



lemma "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct )
        apply (auto)
  done

lemma "(is_nnf (nnf b))"
  apply (induction b rule: nnf.induct)
        apply (auto)
  done

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (AND (OR a1 a2) b2) = False  "
| "is_dnf (AND b1 (OR a1 a2)) = False"
| "is_dnf (AND b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
| "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
| "is_dnf b1 = is_nnf b1"

value "is_nnf (VAR ''x'')"
value "is_dnf (VAR ''x'')"
value "is_dnf (AND (AND (OR (VAR ''x'') (VAR ''x'')) (VAR ''x'')) (VAR ''x''))"


(*
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (AND (OR a1 a2) b2) = OR (AND (dnf_of_nnf a1) (dnf_of_nnf b2)) (AND (dnf_of_nnf a2) (dnf_of_nnf b2)) "
| "dnf_of_nnf (AND b1 (OR a1 a2)) = OR (AND (dnf_of_nnf a1) (dnf_of_nnf b1)) (AND (dnf_of_nnf a2) (dnf_of_nnf b1))"
| "dnf_of_nnf (AND b1 b2) = AND (dnf_of_nnf b1) (dnf_of_nnf b2)"
| "dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)"
| "dnf_of_nnf (VAR b1) = VAR b1"
| "dnf_of_nnf (NEG b1) = NEG b1"

value "dnf_of_nnf (VAR ''x'')"
(*pushes or one thing further out, not all the way*)
(*redo work bottom up. start inside*)
value "dnf_of_nnf (AND (AND (OR (VAR ''x'') (VAR ''x'')) (VAR ''x'')) (VAR ''x''))"
*)

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dist_AND b1 (OR a1 a2)  = OR (dist_AND b1 a1) (dist_AND b1 a2)"
| "dist_AND (OR a1 a2) b2  = OR (dist_AND a1 b2) (dist_AND a2 b2)"
| "dist_AND a1 a2 = AND a1 a2"


lemma pbval_andb [simp]: "pbval (dist_AND a b) s = pbval (AND a b) s"
apply (induction a b rule: dist_AND.induct)
apply (auto)
done

lemma is_dnf_dist [simp]: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
apply (induction b1 b2 rule: dist_AND.induct)
apply (auto)
done


fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1)(dnf_of_nnf b2)"
| "dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)"
| "dnf_of_nnf (VAR b1) = VAR b1"
| "dnf_of_nnf (NEG b1) = NEG b1"


value "dnf_of_nnf (VAR ''x'')"
value "dnf_of_nnf (AND (AND (OR (VAR ''x'') (VAR ''x'')) (VAR ''x'')) (VAR ''x''))"

lemma "((pbval (dnf_of_nnf b1) s)\<and> (pbval (dnf_of_nnf b2) s)) \<Longrightarrow> pbval (dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)) s"
  apply(induction b1 b2 arbitrary: s rule: dist_AND.induct)
           apply(auto)
  done

lemma " (pbval (dnf_of_nnf b) s = pbval b s)"
  apply(induction b rule: dnf_of_nnf.induct)
                 apply(auto)
  done
  

lemma "(is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b))"
  apply(induction b rule: dnf_of_nnf.induct)
                 apply (auto split: pbexp.split)
  done
  

(* exercise 3.11*)
type_synonym reg = "nat"
type_synonym rstate = "reg \<Rightarrow> val"
type_synonym stack = "val list"

datatype instr = LDI val reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec1 (LDI i r) s rg = rg(r:= i)"
(*this one below has s because LD loads value of x. Above loads just i*)
| "exec1 (LD x r) s rg = rg(r:= (s x))"
| "exec1 (ADD r1 r2) s rg = rg(r1 := (rg r1) + (rg r2))"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec [] s rg = rg"
| "exec (i#is) s rg = exec is s (exec1 i s rg)"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (V x) r = [LD x r]"
| "comp (N n) r = [LDI n r]"
| "comp (Plus a1 a2) r = comp a1 (r) @ comp a2 (r + 1) @ [ADD (r) (r+1)]" 



lemma exec_app[simp]: "exec (xs @ ys) s rs = exec ys s (exec xs s rs)"
  apply (induction xs arbitrary: rs)
  apply (auto)
  done

(*this I found online and dont understand yet*)
lemma comp_respects [simp]: "r < q \<Longrightarrow> exec (comp a q) s rs r = rs r"
apply (induction a arbitrary: rs r q)
apply (auto)
done


lemma "exec (comp a r ) s rs r = aval a s"
  apply(induction a arbitrary: rs r)
  by (auto)
  


end