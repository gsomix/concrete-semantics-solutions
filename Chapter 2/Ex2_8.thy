theory Ex2_8
  imports Main
begin

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # xs) = x # a # (intersperse a xs)"

value "intersperse True [False, False, False]"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
    apply(auto)
  done

end