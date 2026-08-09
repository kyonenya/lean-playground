import Mathlib
open Set

variable {U : Type}

-- Subset World

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
    A ⊆ A := by -- ∃x, x ∈ A → x ∈ A
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

-- Complement World

example
    (x : U)
    (A B : Set U)
    (h1 : x ∈ A)
    (h2 : x ∉ B) : -- ¬ (x ∈ A) \nin
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

axiom Subset.antisymm
    (A B : Set U)
    (h1 : A ⊆ B)
    (h2 : B ⊆ A) :
    A = B

theorem _compl_compl
    (A : Set U) :
    Aᶜᶜ = A := by
  apply Subset.antisymm
  -- case h1
  intro x h
  repeat rw [mem_compl_iff x] at h
  push Not at h -- ¬ x ∉ A ↔ ¬¬ x ∈ A → x ∈ A
  exact h
  -- case h2
  intro x h
  repeat rw [mem_compl_iff x]
  push Not
  exact h

example
    (A B : Set U) :
    A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  -- case right
  intro h
  apply compl_subset_compl_of_subset A B at h
  exact h
  -- case left
  intro h
  apply compl_subset_compl_of_subset Bᶜ Aᶜ at h
  repeat rw [_compl_compl A, _compl_compl B] at h
  exact h

-- Intersection World
