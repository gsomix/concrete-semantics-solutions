theory Ex2_4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

value "snoc [False, False, False] True"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse [True, False, False]"
value "reverse (snoc [False, False, False] True)"

lemma revsnoc [simp]: "reverse (snoc xs x) = x # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

theorem revrev: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

end