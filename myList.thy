theory myList
  imports Main
begin

declare[[names_short]]

datatype 'a list = Nil | Cons 'a  "'a list"
(*'a represents that its a list of an arbitrary type. sometimes 'a called alpha*)



value "Cons (4::int) Nil"
(*must specify type bc arbitrary. all elements in list same type*)
value "Cons (2::int) (Cons 3 Nil)"

(* app appends*)
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys" 
| "app (Cons x xs) ys = Cons x(app xs ys)"
(*x is an element of type 'a*)

(*Cons is funtion that creates list of type 'a element x in given list xs (or something. confusing) *)

(*first case base case. second case indutive step*)

(*rev reverses elements*)
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" 
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

lemma app_Nil2 [simp] : "app xs Nil = xs"
  apply (induction xs)
   apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
   apply (auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
   apply (auto)
  done
(*sorry makes lemma valid even if not proved*)

lemma "rev (rev xs) = xs"
  apply (induction xs)
   apply (auto)
  done
(*cant solve by auto, must create additional lemmas(shown above)*)


(*SYNTACTIC SUGAR below. make reference to other calls and functions*)
value "Cons (1 :: nat) Nil"
(*below and above do 2 types of lists.top list is local, bottom list is global; based on notation *)
value "(1 :: nat) # []"
value "[(1 :: nat), 2, 3, 4]"
(* @ is using the app() func *)
value "[1,2,3] @ [4,5,6] :: nat List.list"
value "length [1,2, (3 :: nat)]"
(*returns first element in list*)
value "hd [(1 :: int), 2, 3]"
(*returns list without first element in list*)
value "tl [(1 :: int), 2, 3]"

(*List.list uses global list definition and not the one defined above*)
fun add1 :: "nat List.list \<Rightarrow> nat List.list" where
 "add1 [] = []"
|"add1 (x # xs) = (x + 1) # add1( xs)"

value "add1 [1,2,3] :: nat List.list"

fun plus1 :: "nat \<Rightarrow> nat" where
  "plus1 x = x + 1"

(*map applies a function to every element of a list. a lamda function is a nameless function, introduced on the spot*)
fun add1p :: "nat List.list \<Rightarrow>nat List.list" where
  "add1p xs = map (\<lambda>x. x + 1) xs"

text \<open>
  [1, 2, 3] = 1 # 2 # 3 # []
\<close>


end