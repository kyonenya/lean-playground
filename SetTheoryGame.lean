import Mathlib

-- この世界における集合の要素は、Uと呼ばれる宇宙から得られる。対象 x が宇宙 U に属することを示すには、x : U と書く。A が U からの対象の集合であることを示すには、A : Set U と書く。（Lean で用いられる用語では、x の型は U、A の型は Set U である。） x が A の要素であることを表すには、x ∈ A と記述します。（記号 ∈ は、\mem または \in を入力し、その後にスペースを入れることで入力できます。）

-- AとBが集合である場合、Aのすべての要素がBの要素でもあるとき、AはBの部分集合であると言います。表記A ⊆ Bは、AがBの部分集合であることを意味します。（記号⊆を入力するには、\subと入力し、続けてスペースを入れます。）


open Set

variable {U : Type}


example
    (x : U) -- 対象 x は宇宙 U に属する
    (A : Set U) -- A は U からの対象の集合である
    (h : x ∈ A) : -- x は A の要素である \in
  x ∈ A := by
  exact h

example
    (x : U)
    (A B : Set U)
    (h1 : A ⊆ B) -- x ∈ A → x ∈ B, 部分集合 \sub
    (h2 : x ∈ A) :
    x ∈ B := by
  exact h1 h2

example
    (x : U)
    (A B C : Set U)
    (h1 : A ⊆ B)
    (h2 : B ⊆ C)
    (h3 : x ∈ A) :
  x ∈ C := by
  have h4 : x ∈ B := h1 h3 -- have
  exact h2 h4

example
    (x : U)
    (A B C : Set U)
    (h1 : A ⊆ B)
    (h2 : x ∈ B → x ∈ C) :
    x ∈ A → x ∈ C := by
  intro h3 -- intro
  have h4 : x ∈ B := h1 h3
  exact h2 h4

theorem Subset.refl
    (A : Set U) :
    A ⊆ A := by -- x ∈ A → x ∈ A
  intro h h2 -- destructure definition
  exact h2

theorem Subset.trans
    (A B C : Set U)
    (h1 : A ⊆ B)
    (h2 : B ⊆ C) :
    A ⊆ C := by
  intro x h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4

example
    (x : U)
    (A B : Set U)
    (h1 : x ∈ A)
    (h2 : x ∉ B) : -- \nin
    ¬A ⊆ B := by -- A ⊆ B → False
  by_contra h3 -- goal is a negative statement
  have h4 : x ∈ B := h3 h1
  exact h2 h4

theorem mem_compl_iff
    (x : U)
    (A : Set U) :
    x ∈ Aᶜ ↔ x ∉ A := by -- 補集合 \compl
  rfl -- ↔ \iff  と =

theorem compl_subset_compl_of_subset
    (A B : Set U)
    (h : A ⊆ B) :
    Bᶜ ⊆ Aᶜ := by
  intro x h2
  rw [mem_compl_iff x A]
  by_contra h3
  have h4 : x ∈ B := h h3
  rw [mem_compl_iff x B] at h2
  exact h2 h4
