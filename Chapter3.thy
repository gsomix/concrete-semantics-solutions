theory Chapter3
imports "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/ASM"
begin

text{*
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
*}

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus l r) = (optimal l & optimal r)"

text{*
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
*}

lemma "optimal (asimp_const a)"
  apply(induction a)
    apply(auto split: aexp.split)
  done

text{*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
*}

fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N n) = n" |
"sumN (V x) = 0" |
"sumN (Plus l r) = sumN l + sumN r"

fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N n) = N 0" |
"zeroN (V x) = V x" |
"zeroN (Plus l r) = Plus (zeroN l) (zeroN r)"

text {*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*}

definition sepN :: "aexp \<Rightarrow> aexp" where
"sepN exp = Plus (zeroN exp)  (N (sumN exp))"

lemma aval_sepN: "aval (sepN t) s = aval t s"
  apply(simp add: sepN_def)
  apply(induction t)
    apply(auto)
  done

text {*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*}

definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp exp = asimp (sepN exp)"

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
  apply(simp add: full_asimp_def aval_sepN)
  done

text{*
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*}

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else V y)" |
"subst x a (Plus l r) = Plus (subst x a l) (subst x a r)"

text{*
such that @{term "subst x a e" } is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*}

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
    apply(auto)
  done

text {*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*}
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(simp add: subst_lemma)
  done

text{*
\endexercise

\exercise
Take a copy of theory @{theory AExp} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}

text{*
\endexercise

\exercise
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*}

datatype aexp2 =
    Const int 
  | Var vname
  | PlusOp aexp2 aexp2
  | IncOp vname
  | DivOp aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" 
  where
    "aval2 (Const n) s = Some (n, s)"
  | "aval2 (Var x) s = Some (s x, s)"
  | "aval2 (PlusOp l r) s =
      Option.bind (aval2 l s) (\<lambda> (lval, s\<^sub>1). 
        Option.bind (aval2 r s\<^sub>1) (\<lambda> (rval, s\<^sub>2).
          Some (lval + rval, s\<^sub>2)))"
  | "aval2 (IncOp x) s = Some (s x, s(x := s x + 1))"
  | "aval2 (DivOp l r) s =
      Option.bind (aval2 l s) (\<lambda> (lval, s\<^sub>1). 
        Option.bind (aval2 r s\<^sub>1) (\<lambda> (rval, s\<^sub>2).
          if rval = 0 then None else Some (lval div rval, s\<^sub>2)))"

value "aval2 (PlusOp (IncOp ''x'') (DivOp (Const 5) (Var ''x''))) (<''x'' := -1>)"

text{*
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int"
  where
    "lval (Nl n) s = n"
  | "lval (Vl x) s = s x"
  | "lval (Plusl l r) s = lval l s + lval r s"
  | "lval (LET x e\<^sub>1 e\<^sub>2) s = lval e\<^sub>2 (s(x := lval e\<^sub>1 s))"

value "lval 
        (LET ''x'' (Nl 5)
          (Plusl (Vl ''x'') (Nl 5))) <>"

fun inline :: "lexp \<Rightarrow> aexp"
  where
    "inline (Nl n) = N n"
  | "inline (Vl x) = V x"
  | "inline (Plusl l r) = Plus (inline l) (inline r)"
  | "inline (LET x e\<^sub>1 e\<^sub>2) = subst x (inline e\<^sub>1) (inline e\<^sub>2)"

lemma "lval e s = aval (inline e) s"
  apply(induction e arbitrary: s)
     apply(auto simp add: subst_lemma)
  done

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
*}

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or e\<^sub>1 e\<^sub>2 = Not (And (Not e\<^sub>1) (Not e\<^sub>2))"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq e\<^sub>1 e\<^sub>2 = And (Not (Less e\<^sub>1 e\<^sub>2)) (Not (Less e\<^sub>2 e\<^sub>1))"

value "bval (Eq (N 5) (Plus (N 3) (V ''x''))) <''x'' := 2>"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le e\<^sub>1 e\<^sub>2 = Or (Eq e\<^sub>1 e\<^sub>2) (Less e\<^sub>1 e\<^sub>2)"

value "bval (Le (N 5) (Plus (N 3) (V ''x''))) <''x'' := 3>"

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(simp add: Eq_def)
  apply(auto)
  done

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(simp add: Le_def Eq_def Or_def)
  apply(auto)
  done

text{*
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional: *}

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text {*  First define an evaluation function analogously to @{const bval}: *}

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" 
  where
    "ifval (Bc2 b) s = b"
  | "ifval (If e\<^sub>1 e\<^sub>2 e\<^sub>3) s = 
      (if ifval e\<^sub>1 s then 
         ifval e\<^sub>2 s 
       else 
         ifval e\<^sub>3 s)"
  | "ifval (Less2 a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

text{* Then define two translation functions *}

fun b2ifexp :: "bexp \<Rightarrow> ifexp" 
  where
    "b2ifexp (Bc b) = Bc2 b"
  | "b2ifexp (Not e) = (If (b2ifexp e) (Bc2 False) (Bc2 True))"
  | "b2ifexp (And e\<^sub>1 e\<^sub>2) =
      (If (b2ifexp e\<^sub>1) 
        (If (b2ifexp e\<^sub>2) 
          (Bc2 True) 
          (Bc2 False)) 
        (Bc2 False))"
  | "b2ifexp (Less a\<^sub>1 a\<^sub>2) = Less2 a\<^sub>1 a\<^sub>2"

(* if a then b else c \<equiv> (a \<and> b) \<or> (\<not>a \<and> c) *)
fun if2bexp :: "ifexp \<Rightarrow> bexp" 
  where
    "if2bexp (Bc2 b) = Bc b"
  | "if2bexp (If e\<^sub>1 e\<^sub>2 e\<^sub>3) = 
      (let be\<^sub>1 = if2bexp e\<^sub>1 in
        Or (And      be\<^sub>1  (if2bexp e\<^sub>2)) 
           (And (Not be\<^sub>1) (if2bexp e\<^sub>3)))"
  | "if2bexp (Less2 a\<^sub>1 a\<^sub>2) = Less a\<^sub>1 a\<^sub>2"

text{* and prove their correctness: *}

lemma "bval (if2bexp exp) s = ifval exp s"
  apply(induction exp arbitrary: s)
    apply(auto simp add: Let_def Or_def)
  done

lemma "ifval (b2ifexp exp) s = bval exp s"
  apply(induction exp arbitrary: s)
     apply(auto)
  done

text{*
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
*}

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text{*
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
*}

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool"
  where
    "pbval (VAR x) s = s x"  
  | "pbval (NOT b) s = (\<not> pbval b s)" 
  | "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" 
  | "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)" 

text {* Define a function that checks whether a boolean expression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s: *}

fun is_nnf :: "pbexp \<Rightarrow> bool" 
  where
    "is_nnf (VAR x) = True"
  | "is_nnf (NOT (VAR x)) = True"
  | "is_nnf (NOT b) = False"
  | "is_nnf (AND b\<^sub>1 b\<^sub>2) = (is_nnf b\<^sub>1 & is_nnf b\<^sub>2)"
  | "is_nnf (OR b\<^sub>1 b\<^sub>2) = (is_nnf b\<^sub>1 & is_nnf b\<^sub>2)" 

text{*
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
*}

fun nnf :: "pbexp \<Rightarrow> pbexp" 
  where
    "nnf (VAR x) = VAR x"
  | "nnf (NOT (AND b\<^sub>1 b\<^sub>2)) = OR (nnf (NOT b\<^sub>1)) (nnf (NOT b\<^sub>2))"
  | "nnf (NOT (OR b\<^sub>1 b\<^sub>2)) = AND (nnf (NOT b\<^sub>1)) (nnf (NOT b\<^sub>2))"
  | "nnf (NOT (NOT b)) = nnf b"
  | "nnf (AND b\<^sub>1 b\<^sub>2) = AND (nnf b\<^sub>1) (nnf b\<^sub>2)"
  | "nnf (OR b\<^sub>1 b\<^sub>2) = OR (nnf b\<^sub>1) (nnf b\<^sub>2)"
  | "nnf b = b"

text{*
Prove that @{const nnf} does what it is supposed to do:
*}

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
  apply(induction b arbitrary:s rule:nnf.induct)
    apply(auto)
  done

lemma is_nnf_nnf: "is_nnf (nnf b)"
  apply(induction b rule:nnf.induct)
    apply(auto)
  done

text{*
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
*}

fun is_dnf :: "pbexp \<Rightarrow> bool" 
  where
    "is_dnf (AND (OR _ _) _) = False"
  | "is_dnf (AND _ (OR _ _)) = False"
  | "is_dnf (AND b\<^sub>1 b\<^sub>2) = (is_dnf b\<^sub>1 & is_dnf b\<^sub>2)"
  | "is_dnf (OR b\<^sub>1 b\<^sub>2) = (is_dnf b\<^sub>1 & is_dnf b\<^sub>2)"
  | "is_dnf b = is_nnf b"

value "is_dnf (OR (AND (VAR ''A'') (VAR ''B'')) (NOT (VAR ''A'')))"
value "is_dnf (NOT (OR (VAR ''A'') (VAR ''B'')))"
value "is_dnf (OR (VAR ''A'') 
                  (AND (VAR ''B'') 
                       (OR (VAR ''C'') 
                           (VAR ''D''))))"

text {*
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
*}

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" 
  where
    "dist_AND b (OR c\<^sub>1 c\<^sub>2) = OR (dist_AND b c\<^sub>1) (dist_AND b c\<^sub>2)"
  | "dist_AND (OR b\<^sub>1 b\<^sub>2) c = OR (dist_AND b\<^sub>1 c) (dist_AND b\<^sub>2 c)"
  | "dist_AND b c = AND b c"

value "dist_AND (OR (VAR ''A1'') (VAR ''A2''))
                (OR (VAR ''B1'') (VAR ''B2''))"


text {* and prove that it behaves as follows: *}

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
  apply(induction b1 b2 arbitrary:s rule:dist_AND.induct)
    apply(auto)
  done

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
  apply(induction b1 b2 rule:dist_AND.induct)
    apply(auto)
  done

text {* Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
*}

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp"
  where
    "dnf_of_nnf (AND b\<^sub>1 b\<^sub>2) = dist_AND (dnf_of_nnf b\<^sub>1) (dnf_of_nnf b\<^sub>2)"
  | "dnf_of_nnf (OR b\<^sub>1 b\<^sub>2) = OR (dnf_of_nnf b\<^sub>1) (dnf_of_nnf b\<^sub>2)"
  | "dnf_of_nnf b = b"

text {* Prove the correctness of your function: *}

lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply(induction b arbitrary:s rule:dnf_of_nnf.induct)
    apply(auto simp add:pbval_dist)
  done

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply(induction b rule: dnf_of_nnf.induct)
    apply(auto simp add:is_dnf_dist)
  done

text{*
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than two. In our semantics
stack underflow leads to a term involving @{term "hd []"},
which is not an error or exception --- HOL does not
have those concepts --- but some unspecified value. Modify
theory @{theory ASM} such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
*}

text{*
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
*}
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text {*
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state: *}

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" 
  where
    "exec1 (LDI v r) _ rs = rs(r := v)"
  | "exec1 (LD vn r) s rs = rs(r := s vn)"
  | "exec1 (ADD r\<^sub>1 r\<^sub>2) _ rs = rs(r\<^sub>1 := rs r\<^sub>1 + rs r\<^sub>2)"

text{*
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.*}

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate"
  where
    "exec [] _ rs = rs"
  | "exec (x#xs) s rs = exec xs s (exec1 x s rs)"

value "exec [LDI 2 0, LDI 2 1, ADD 0 1] <> <> 0"
value "exec [LDI 2 0, LD ''x'' 1, ADD 0 1] <''x'' := 3> <> 0"

text{* 
The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
*}

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" 
  where
    "comp (N n) r = [LDI n r]"
  | "comp (V x) r = [LD x r]"
  | "comp (Plus e\<^sub>1 e\<^sub>2) r = comp e\<^sub>1 r @ comp e\<^sub>2 (r+1) @ [ADD r (r+1)]"

value "comp (Plus (N 2) (N 2)) 0"
value "comp (Plus (Plus (N 1) (N 2)) (Plus (N 1) (N 0))) 0"

value "exec (comp 
              (Plus (Plus (N 2) (N 2)) (Plus (N 1) (N 5)))
              0)
            <>
            <>
            0"

lemma exec_append: "exec (p\<^sub>1 @ p\<^sub>2) s rs = exec p\<^sub>2 s (exec p\<^sub>1 s rs)"
  apply(induction p\<^sub>1 arbitrary: rs)
   apply(auto)
  done

lemma exec_safe: "rn > r \<Longrightarrow> exec (comp a rn) s rs r = rs r"
  apply(induction a arbitrary: r rn rs)
    apply(auto simp add: exec_append)
  done

theorem "exec (comp a r) s rs r = aval a s"
  apply(induction a arbitrary: r rs)
    apply(auto simp add: exec_append exec_safe)
  done

text{*
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
*}

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text{*
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
*}

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate"
  where
    "exec01 (LDI0 n) s rs = rs(0 := n)"
  | "exec01 (LD0 vn) s rs = rs(0 := s vn)"
  | "exec01 (MV0 r) s rs = rs(r := rs 0)"
  | "exec01 (ADD0 r) s rs = rs(0 := rs 0 + rs r)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate"
  where
    "exec0 [] s rs = rs"
  | "exec0 (x#xs) s rs = exec0 xs s (exec01 x s rs)"

text{*
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
*}

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list"
  where
    "comp0 (N n) r = [LDI0 n]"
  | "comp0 (V x) r = [LD0 x]"
  | "comp0 (Plus e\<^sub>1 e\<^sub>2) r = comp0 e\<^sub>1 r @ [MV0 (r+1)] @ comp0 e\<^sub>2 (r+1) @ [ADD0 (r+1)]"

lemma comp0_append: "exec0 (p\<^sub>1 @ p\<^sub>2) s rs = exec0 p\<^sub>2 s (exec0 p\<^sub>1 s rs)"
  apply(induction p\<^sub>1 arbitrary: rs)
   apply(auto)
  done

lemma comp0_safe: "\<lbrakk>r \<noteq> 0 \<and> rn \<ge> r\<rbrakk> \<Longrightarrow> exec0 (comp0 a rn) s rs r = rs r"
  apply(induction a arbitrary: r rn rs)
    apply(auto simp add: comp0_append)
  done

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r rs)
    apply(auto simp add: comp0_append comp0_safe)
  done

text{*
\endexercise
*}

end

