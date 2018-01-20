theory Ex2_10
imports 
    Main
begin

datatype tree0 = Leaf | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes (Leaf) = 1" |
"nodes (Node l r) = Suc ((nodes l) + (nodes r))"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

theorem nodes_explode: "(let l = nodes t in nodes (explode n t) = (2^n) * l + (2^n) - 1)"
  apply(simp add: Let_def)
  apply(induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

end