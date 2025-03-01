theory Recursion
  imports Main
begin

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []"
| "rev (x # xs) = (rev xs) @ [x]"

value "rev [a , b, c]"


(*this is called tail-recursive because there is no stack,when done with append there is a stack. This avoids overloading the stack*)
(*it is important to shoot for tail recursive functions*)
(*generally consists of adding an element to the function where we accumulate the result*)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []       ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

(*testing proves only that it works on test, not globaly*)
value "itrev [a ,b ,c] []"


lemma "itrev xs ys  = rev xs @ ys"
(*arbitrary says that it applies for all ys, not any single ys*)
  apply (induction xs arbitrary: ys)
   apply (auto)
  done

end