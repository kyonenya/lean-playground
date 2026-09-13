import LeanBook.Ch8_2_Mul_Ring

/-- 定数関数を返す-/
private def MyInt.const (z : MyInt) : MyInt → MyInt :=
  fun _ => z

#check_failure MyInt.const (0 : MyNat)

/-- 自然数から整数への変換 -/
def MyInt.ofMyNat (n : MyNat) : MyInt :=
  ⟦(n, 0)⟧

-- エラーが消える
#check MyInt.const (.ofMyNat 0)

-- Coe 整数が期待されている場所に自然数が現れたら、自動的に整数への変換が施されるようにしたい

/-- MyNat からMyInt への型強制-/
instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat)

-- [coe] ofMyNat という内部実装を隠蔽する

-- MyInt.ofMyNat を型キャストとして認識させる
attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofMyNat_zero_eq_zero :
    MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [MyInt.ofMyNat]
  rfl

-- 内部実装を意識しなくて済むようになった
example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- MyInt.ofMyNat (0 : MyNat) = (0 : MyInt)
  -- ↑ (0 : MyNat) = (0 : MyInt)
  -- [↑：文脈が要求する上位の型へ持ち上げること（MyNat→MyInt）]
  simp

-- 自然数から整数への写像は「大きいほうの集合に送る」だけなので単射


/-- 自然数 m, n を MyInt にキャストしたあとで等しい
      ↔
    もともと自然数として等しい -/
@[norm_cast] -- 型キャスト専用のタクティク
theorem MyInt.ofMyNat_inj {m n : MyNat}
    : (m : MyInt) = (n : MyInt) ↔ m = n := by
  constructor <;> intro h
  case mp =>
    -- このとき、(m, 0) と(n, 0) はPreInt として同値である
    have : (m, 0) ≈ (n, 0) := by
      exact Quotient.exact h
    simp only [sr_def] at this
    simp_all
  case mpr =>
    rw [h]

@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat}
    : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  case mp =>
    rw [show (0 : MyInt) = ↑ (0 : MyNat) from rfl] at h
    norm_cast at h -- 仮定h : ↑n = ↑0の型キャストを外したい
  case mpr =>
    simp_all

/-- ↑ (a + b) を ↑a + ↑b にしたい -/
@[push_cast]
theorem MyInt.ofNat_add (m n : MyNat)
: ↑ (m + n) = (m : MyInt) + (n : MyInt) := by
  rfl
