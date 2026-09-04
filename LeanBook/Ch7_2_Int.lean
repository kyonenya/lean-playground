import LeanBook.Ch7_1_Quotient

/-- 自然数を 2 つペアにしたもの -/
abbrev PreInt := MyNat × MyNat

/-- x₁ - y₁ = x₂ - y₂ -/
def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

theorem PreInt.r.refl :
    ∀ (m : PreInt), r m m := by
  intro (m₁, m₂)
  dsimp [r]
  ac_rfl

theorem PreInt.r.symm :
    ∀ {m n : PreInt}, r m n → r n m := by
  intro (m₁, m₂) (n₁, n₂) h
  dsimp [r] at *
  replace h : m₂ + n₁ = m₁ + n₂ := by exact h.symm
  rw [MyNat.add_comm m₁, MyNat.add_comm m₂] at h
  exact h

theorem PreInt.r.trans :
    ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
  dsimp [r] at *
  have : m₁ + (l₁ + n₂) = m₁ + (l₂ + n₁) := calc
    _ = m₁ + n₂ + l₁ := by ac_rfl
    _ = m₂ + n₁ + l₁ := by rw [hmn]
    _ = l₁ + m₂ + n₁ := by ac_rfl
    _ = l₂ + m₁ + n₁ := by rw [hlm]
    _ = m₁ + (l₂ + n₁) := by ac_rfl
  simp_all only [↓MyNat.add_left_cancel_iff]

theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl, symm := r.symm, trans := r.trans }

/-- PreInt 上の同値関係 -/
@[instance] def PreInt.sr : Setoid PreInt :=
  ⟨r, r.equiv⟩

/-- MyNat × MyNat を同値関係で割ることで構成した整数 -/
abbrev MyInt := Quotient PreInt.sr

#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a -- PreInt.sr は _ で推論させて省略できる

/-- 同値類を表す記法 -/
notation:arg (priority := low) "⟦" a "⟧" => Quotient.mk _ a

#check (⟦(1, 3)⟧ : MyInt)

def MyInt.ofNat (n : Nat) : MyInt :=
  ⟦(MyNat.ofNat n, 0)⟧

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)

-- ### マイナス記号を作る

-- 整数の符号反転はペアの左右を交換すればよい
-- - ⟦(m, n)⟧ = ⟦(n, m)⟧

-- 代表元について左右を交換する関数
def PreInt.neg : PreInt → MyInt
  | (m, n) => ⟦(n, m)⟧
-- (4, 0) ↦ ⟦(0, 4)⟧

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  -- PreInt.neg が同値関係を保つことを示したい
  -- (a₁, a₂) : PreInt と(b₁, b₂) : PreInt が同値だと仮定する
  intro (a₁, a₂) (b₁, b₂) hab
  -- このときneg (a₁, a₂) = neg (b₁, b₂) を示せばよいのだが
  -- 商空間におけるneg の定義により(a₂, a₁) ≈ (b₂, b₁) を示せばよい
  suffices (a₂, a₁) ≈ (b₂, b₁) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption
  -- しかしこれは同値性の定義と仮定より明らか
  notation_simp at *
  simp_all

-- MyInt に対して - が来たら、さっき作った MyInt.neg を使ってください
instance : Neg MyInt where
neg := MyInt.neg

#check (-4 : MyInt)

-- r はα 上の二項関係とする
variable {α : Type} {r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
: ∀ {x y : α}, r x y → r y x := by
  intro x y hxy
  have h2 : ∀ (x y : α), r x x → r x y → r y x := by
    intro x y
    exact h x x y
  have hxx : r x x := by exact refl x
  exact h2 x y hxx hxy

private theorem Ex.equiv (refl : ∀ x, r x x)
(h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor
  case refl => exact refl
  case symm => exact Ex.symm refl h
  case trans =>
    intro x y z hxy hyz
    have hzx := by exact h x y z hxy hyz
    exact Ex.symm refl h hzx
