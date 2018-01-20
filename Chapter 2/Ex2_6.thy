theory Ex2_6
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node t1 v t2) = v # (contents t1) @ (contents t2)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node t1 v t2) = v + (sum_tree t1) + (sum_tree t2)"

theorem sumtree_contents : "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

end