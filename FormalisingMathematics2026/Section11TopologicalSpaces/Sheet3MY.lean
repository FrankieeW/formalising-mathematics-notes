import Mathlib.Tactic

example {z : ℤ }:(z : ℚ)=(z : ℚ) := by
  -- this is a bit weird, but it works!
  exact rfl

variable {G : Type*} [Group G] (H : Subgroup G)

example (g : H) : g  =  g := by
  -- this is a bit weird, but it works!
  -- exact rfl
  obtain ⟨ g' , hg'⟩  := g
  rfl

variable {G' : Type*} [Group G'] (f g : G →* G')

example :(f : G →* G') = g := by
  -- this is a bit weird, but it works!
  -- exact rfl
  show_term ext x
  sorry

-- parser : 解析器 - - parser 是一个程序，
-- 负责将 Lean 代码转换成 Lean 内部的抽象语法树（AST）。
-- 它处理 Lean 代码中的语法结构，并将其转换为 Lean 内部可以理解的形式。

-- elaborator : 细化器 - - elaborator 是一个更强大的 parser，能够处理 Lean 代码中的隐式参数、类型类实例等复杂情况。

-- compiler : 编译器 - - compiler 是将 Lean 内部的抽象语法树（AST）转换成 Lean 的核心语言（Core Language）的程序。
-- Lean 的核心语言是一种更底层的表示形式，适合进行类型检查和执行。

-- kernel : 内核 - - kernel 是 Lean 的核心组件，负责执行类型检查、证明验证等关键任务。

-- noncomputable : 非可计算的 - - noncomputable 是 Lean 中的一个标记，表示某个定义或证明是非可计算的。
-- Lean dosen't know how to write code for your def

-- nonconstructive : 非构造性的 - - nonconstructive 是 Lean 中的一个标记，表示某个定义或证明是非构造性的。
-- lean uses the axiom of choice to make your def/thm

#check Classical.choice
#print axioms riesz_lemma

#check em
example (P : Prop) : P ∨ ¬ P := by
  -- this is the law of excluded middle, which is an axiom in Lean
  exact em P
