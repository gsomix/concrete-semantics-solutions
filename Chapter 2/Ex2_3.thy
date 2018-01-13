theory Ex2_3
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # ys) = (if y = x then Suc (count x ys) else count x ys)"

value "count True [True, False, False, True, True]"

theorem countLessThanLength: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

end