theory Assignment_05
imports Main
begin

(*exercise 2.10 pg 35*)
datatype tree0 = Tip | Node "tree0" "tree0"
definition empty :: "tree0" where "empty \<equiv> Tip"
definition singleton where "singleton \<equiv> Node Tip Tip"


(*datatype 'a atree = Tip | Node "'a atree" 'a "'a atree" *)

value " Node  (Node Tip  Tip) Tip "

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 0"
| "nodes (Node l r) =1 + nodes(l) + nodes (r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"


value " Node  (Node Tip  Tip) Tip "

value "nodes(Node  (Node Tip  Tip) Tip)"
value "nodes (explode 0 (Node (Node Tip  Tip) Tip)) "
value "nodes (explode 1 (Node (Node Tip  Tip) Tip)) "
value "nodes (explode 2 (Node (Node Tip  Tip) Tip)) "


value "Node  (Node singleton singleton) (Node singleton singleton)"

value "nodes(Node  (Node singleton singleton) (Node singleton singleton))"
value "nodes (explode 0 (Node  (Node singleton singleton) (Node singleton singleton))) "
value "nodes (explode 1 (Node  (Node singleton singleton) (Node singleton singleton))) "
value "nodes (explode 2 (Node  (Node singleton singleton) (Node singleton singleton))) "

value "nodes(Node  (Node singleton singleton) (Node singleton singleton)) * 2 ^ 2 +2^2 - 1"

fun size_exp :: " nat \<Rightarrow> tree0 \<Rightarrow> nat" where
  "size_exp n t = nodes(t) * 2 ^ n + 2^n - 1"

lemma "nodes (explode n t) = nodes(t) * 2 ^ n + 2^n - 1"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
  done

(*exercise 2.11*)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var c = c"
| "eval (Const i) _ = i"
| "eval (Add e1 e2) c = (eval e1 c) + (eval e2 c)"
| "eval (Mult e1 e2) c = (eval e1 c) * (eval e2 c)"

value "eval(Add(Mult(Const 2)Var)(Const 3)) 2"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0"
| "evalp (c # cs) x = c + x * evalp cs x"

value "evalp [1,2,3] 0"
(* 1 + 2x + 3x^2 at x = 0 *)

(*add polynomials*)
fun polyAdd :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "polyAdd [] [] = []"
| "polyAdd [] ys = ys"
| "polyAdd xs [] = xs"
| "polyAdd (x # xs) (y # ys) = (x + y) #  polyAdd xs ys"

value "polyAdd [1,2,3] [1,2,3]"

fun polyScale :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "polyScale n [] = []"
| "polyScale n (x # xs) = (n * x) # (polyScale n xs)"

value "polyScale 3 [1,2,3]"

(*foil polynomials*)
fun polyMult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "polyMult [] [] = []"
| "polyMult xs [] = []"
| "polyMult [] ys = []"
| "polyMult (x # xs) ys = polyAdd (polyScale x ys)  (0 #  polyMult xs ys)"

value "polyMult [2,5][5,-8]"
(*^ this should equal [10, 9, -40]*)

fun coeffs:: "exp \<Rightarrow> int list" where
  "coeffs Var  = [0,1]"
| "coeffs (Const c) = [c] "
| "coeffs (Add e1 e2) = polyAdd (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = polyMult (coeffs e1) (coeffs e2)"

lemma polyAddDistribute [simp]: "evalp (polyAdd e1 e2) x = evalp e1 x + evalp e2 x"
  apply (induction e1 rule: polyAdd.induct)
  apply (auto)
  apply (simp add: algebra_simps)
  done

lemma polyScaleDistribute [simp]: "evalp (polyScale xa va) x = xa * evalp va x " 
  apply (induction arbitrary: x rule: polyScale.induct)
   apply (auto simp add: algebra_simps)
  done
  

lemma polyMultDistribute [simp]: "evalp (polyMult e1 e2) x = evalp e1 x * evalp e2 x"
  apply (induction rule: polyMult.induct)
  apply (auto)
  apply (simp add: algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply (induction e rule: coeffs.induct)
     apply (auto)
  done
   
(*exercise 3.1*)

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

(*I couldn't figure out if there was a preexisting one. \<and> wasn't  working*)
fun AND :: "bool => bool => bool" where
  "AND True True = True"
| "AND False _ = False"
| "AND True False = False"


fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N n) = True"
| "optimal (V x) = True"
| "optimal (Plus (N n1) (N n2)) = False"
| "optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

lemma "optimal (asimp_const a)"
  apply (induction a)
    apply (auto split: aexp.split)
  done

end