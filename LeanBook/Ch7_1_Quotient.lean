import LeanBook.Ch6_3_DecidableOrder

-- ### Equivalence：～は同値関係である

-- iseqv : Equivalence r
-- それが同値関係であるという証明

example {α : Type}
    (r : α → α → Prop)
    (h : Equivalence r) -- rは同値関係である
    : ∀ x, r x x := by
  exact h.refl

-- ### Setoid：同値関係

-- sr : Setoid α
-- α 上の二項関係 r と、それが同値関係であるという証明をまとめたもの

example {α : Type}
    (sr : Setoid α) -- 同値関係としてのr
    (x y : α)
    : sr.r x y = (x ≈ y) := by
  rfl

-- ### Quotient：商

-- A : Quotient sr
-- α の同値関係 sr による商 𝔸 の要素
-- A = ⟦a⟧

-- ### Quotient.mk：同値類を取る

-- Quotient.mk : Setoid α → α → 𝔸

-- ⟦·⟧ : Quotient.mk _

-- ⟦a⟧ : Quotient.mk sr a

section
  variable {α β : Type} (sr : Setoid α)

  -- Quotient.mk sr : α → 𝔸
  #check (Quotient.mk sr : α → Quotient sr)

  variable (f : β → α)

  -- (α → 𝔸) ∘ (β → α)
  #check (Quotient.mk sr ∘ f) -- β → 𝔸
end

-- ### Quotient.inductionOn：同値類の代表元を取る

-- P⟦a⟧ <- P(A)

-- P (Quotient.mk sr a₁) <- P (A)
--        (α → 𝔸)

section
  variable {α : Type} (sr : Setoid α)

  example (A : Quotient sr) : True := by
    -- ∀A P(A) を ∀a P(⟦a⟧) に帰着させる
    induction A using Quotient.inductionOn with
    | h a =>
      trivial
end

-- ### Quotient.lift：関数を商へと誘導する

-- f : α → β
-- Quotient.lift f h : 𝔸 → β

-- h : a ≈ a' → f a = f a' (well-definedness)

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β)
  variable (h : ∀ a a', a ≈ a' → f a = f a')

  -- f : α → β
  #check Quotient.lift f h -- F : 𝔸 → β

  example : ∀ a,
      -- (F) (A) = f a
      (Quotient.lift f h) (Quotient.mk sr a) = f a := by
    intro a
    dsimp [Quotient.lift, Quotient.mk]
end

section
  variable {α : Type} (sr : Setoid α)
  variable (a₁ a₂ : α) (h : a₁ ≈ a₂)

-- ### Quotient.sound : ≈ → =

-- a₁ ≈ a₂ → A = A

  /-- ⟦a₁⟧ = ⟦a₂⟧ -/
  example : Quotient.mk sr a₁ = Quotient.mk sr a₂ := by -- A₁ = A₂
    -- 元の世界で同値な二つの元は、商の世界では同じ要素に潰れる
    apply Quotient.sound -- a₁ ≈ a₂ <- A₁ = A₂
    exact h

  variable (p q : α)

-- ### Quotient.exact : ≈ ← =

-- A₁ = A₂ → a₁ ≈ a₂

  example (h : Quotient.mk sr a₁ = Quotient.mk sr a₂) : a₁ ≈ a₂ := by
    -- 商の世界で同じ要素に潰れる二つの元は、元の世界でも同値
    exact Quotient.exact h
end
