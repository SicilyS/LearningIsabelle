theory Assignment_06
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

(*subst x a e is the result of replacing every
occurrence of variable x by a in e*)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a1 (N n) = N n"
| "subst x a1 (V y)  = (if x = y then a1 else V y)"
| "subst x a1 (Plus e1 e2) = Plus (subst x a1 e1) (subst x a1 e2)"

value "subst ''x'' (N 3) (Plus (V ''x'')(V ''y''))"

lemma "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e arbitrary: x)
    apply (auto)
  done

(*exercise 3.4*)
datatype aexp1 = N int | V vname | Plus aexp1 aexp1 | Times aexp1 aexp1

fun aval1 :: "aexp1 \<Rightarrow> state \<Rightarrow> val" where
  "aval1 (N n) s = n" 
| "aval1 (V x ) s = s x" 
| "aval1 (Plus a1 a2) s = aval1 a1 s + aval1 a2 s"
| "aval1 (Times a1 a2) s = aval1 a1 s * aval1 a2 s"

fun plus1 :: "aexp1 \<Rightarrow> aexp1 \<Rightarrow> aexp1" where
  "plus1 (N i1) (N i2) = N (i1 + i2)"
| "plus1 (N i) a  = (if i=0 then a else Plus (N i) a)"
| "plus1 a (N i) = (if i=0 then a else Plus a (N i))"
| "plus1 a1 a2 = Plus a1 a2"

fun times :: "aexp1 \<Rightarrow> aexp1 \<Rightarrow> aexp1" where
  "times (N i1) (N i2) = N (i1 * i2)"
| "times (N i) a  = (if i=0 then N 0 else (if i=1 then a else Times (N i) a))"
| "times a (N i) = (if i=0 then N 0 else (if i=1 then a else Times a (N i)))"
| "times a1 a2 = Times a1 a2"

fun asimp1 :: "aexp1 \<Rightarrow> aexp1" where
  "asimp1 (N n) = N n"
| "asimp1 (V x) = V x"
| "asimp1 (Plus a1 a2) = plus1 (asimp1 a1) (asimp1 a2)"
| "asimp1 (Times a1 a2) = times (asimp1 a1) (asimp1 a2)"

lemma aval_plus1  [simp]: "aval1 (plus1 a1 a2) s = aval1 a1 s + aval1 a2 s"
  apply(induction a1 rule: plus1.induct)
    apply (auto)
  done

lemma aval_times  [simp]: "aval1 (times a1 a2) s = aval1 a1 s * aval1 a2 s"
  apply(induction a1 rule: times.induct)
    apply (auto)
  done

lemma "aval1 (asimp1 a) s = aval1 a s"
  apply (induction a)
     apply (auto)
  done

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

defintion Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  ""

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

fun OR_check :: "pbexp \<Rightarrow> bool" where
  "OR_check (OR b1 b2) = False"
| "OR_check (AND b1 b2) = ((OR_check b1) \<and> (OR_check b2))"
| "OR_check _ = True "

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (AND b1 b2) = (((is_nnf b1) \<and> (OR_check b1)) \<and> ((is_nnf b2) \<and> (OR_check b2)))"
| "is_dnf (OR b1 b2) = ((is_dnf b1) \<and> (is_dnf b2))"
| "is_dnf b1  = is_nnf b1"

fun dnf_of_nnf :: "" where

(* exercise 3.11*)



end