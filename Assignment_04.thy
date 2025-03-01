theory Assignment_04
imports Main
begin



(*
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" 
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
*)

(*rev reverses elements. alt syntax above*)
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev [] = []" 
| "rev ( x # xs) = (rev xs) @ [x]"


(*exercise 2.1*)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*exercise 2.2*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "add 0       b = b"
| "add (Suc a) b = Suc (add a b)"


fun double :: "nat \<Rightarrow> nat" where
  "double a  = add a a"

lemma add0 [simp]: "add x 0 = x"
  apply (induction x)
  by (auto)


lemma add_Suc [simp]: "Suc (add x y) = add x (Suc y)"
  apply (induction x)
  apply (auto)
  done

lemma add1 [simp]: "add x y = add y x"
  apply (induction x)
  apply (auto)
  done


lemma "(double m = add m m)"
  apply (induction m)
   apply (auto)
  done

 
(*exercise 2.3*)
fun count :: "'a \<Rightarrow> 'a List.list \<Rightarrow> nat" where
  "count x []       = 0"
| "count x (y # ys) = (if x = y then 1 else 0) + (count x ys)"

value "count (1 :: nat) [1, 2, 1]"

lemma "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

(*exercise 2.6*)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(**)
definition empty :: "nat tree" where "empty \<equiv> Tip"
definition singleton where "singleton \<equiv> Node Tip (1 :: nat) Tip"

value "empty"
value "singleton"
value "Tip :: nat tree"
value "Node Tip a Tip"
value "sum_tree (Node (Node Tip b Tip) a Tip)"
value "Node singleton 2 singleton"

(* app appends*)
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] ys = ys" 
| "app (Cons x xs) ys = Cons x(app xs ys)"
(*x is an element of type 'a*)


fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = (a # []) @ ( (contents r) @  (contents l)) "

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = a + sum_tree l + sum_tree r"


value "contents (Node (Node Tip b Tip) a Tip)"

lemma "sum_tree t = sum_list(contents t)"
  apply (induction t)
  apply (auto)
  done

(*exercise 2.8*)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse x [] = []"
| "intersperse _ [y] = [y]"
| "intersperse x (y # ys) = y # x # (intersperse x ys)"

value "intersperse 1 ( [(1 :: nat), 2, 3, 4])"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
   apply (auto)
  done

value "intersperse 2 [3::int]"

end
