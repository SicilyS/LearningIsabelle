theory Int
  imports Main
begin

fun sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

fun splice :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "splice xs [] = xs"
| "splice [] ys = ys"
| "splice (x # xs) (y # ys) = x # y # splice xs ys"

lemma "sum (splice xs ys) = sum xs + sum ys"
  apply (induction rule: splice.induct)
  by (auto)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []"
| "intersperse x (y # ys) = y # (if length ys = 0 then [] else y # intersperse x ys)"

value "intersperse 2 [3::int]"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply (auto)
  done

end
