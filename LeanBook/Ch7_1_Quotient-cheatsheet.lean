import LeanBook.Ch6_3_DecidableOrder

variable {α β : Type}
variable {a : α}

-- ## Equivalence：～は同値関係であるという証明
-- iseqv : Equivalence r := { refl, symm, trans }

-- ## Setoid：同値関係 ≈
variable (sr : Setoid α) -- := { r, iseqv := refl, symm, trans }
-- ex) sr.r a b := a ≤ b ∧ b ≤ a

-- ## Quotient：商型 𝔸
#check Quotient sr -- 𝔸 -- 同値関係 sr による商型
variable {A : Quotient sr} -- A : 𝔸 -- 商 𝔸 の要素

-- ## Quotient.mk：同値類を取る ⟦ ⟧
#check Quotient.mk sr   -- ⟦ ⟧ : α → 𝔸
#check Quotient.mk sr a -- ⟦a⟧ : 𝔸

-- ## Quotient.inductionOn：同値類から代表元を取る
-- P A を P ⟦a⟧ に帰着させる
example (A : Quotient sr)
    : ∃ a, Quotient.mk sr a = A := by -- P A
  refine Quotient.inductionOn A ?_ -- ⊢ P ⟦a⟧
  exact fun a => ⟨a, rfl⟩

-- ### Quotient.lift：関数を商へと誘導する

  variable (f : α → β)
  -- αから異なる代表元を選んでも関数結果が同じである保証（がないと商𝔸に下ろせない）
  variable (h : ∀ a a', a ≈ a' → f a = f a') -- well-definedness
  #check Quotient.lift f h -- F : 𝔸 → β

  example : ∀ a,   -- (F) (A) = f a
      (Quotient.lift f h) (Quotient.mk sr a) = f a := by
    intro a
    dsimp [Quotient.lift, Quotient.mk]

-- ### Quotient.sound : ≈ → =
-- a₁ ≈ a₂ → A = A

-- ### Quotient.exact : ≈ ← =
-- A₁ = A₂ → a₁ ≈ a₂

section
  variable {α : Type} (sr : Setoid α)
  variable (a₁ a₂ : α) (h : a₁ ≈ a₂)

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
