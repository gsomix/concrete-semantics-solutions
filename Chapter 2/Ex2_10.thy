theory Ex2_10
imports 
    Main
begin

datatype 'a tree0 = Leaf | Node "'a tree0" "'a tree0"

fun nodes :: "'a tree0 \<Rightarrow> nat" where
"nodes (Leaf) = 1" |
"nodes (Node l r) = Suc ((nodes l) + (nodes r))"

fun explode :: "nat \<Rightarrow> 'a tree0 \<Rightarrow> 'a tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

value "nodes (explode 1 Leaf) = 3"

theorem nodes_explode: "(let l = nodes t in nodes (explode n t) = (2^n) * l + (2^n) - 1)"
  apply(simp add: Let_def)
  apply(induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

end