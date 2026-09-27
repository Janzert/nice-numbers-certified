import NiceNumbers
import NiceCertified.TwoThree.Base2
import NiceCertified.TwoThree.Base3
import NiceCertified.TwoThree.Base4
import NiceCertified.TwoThree.Base5
import NiceCertified.TwoThree.Base6
import NiceCertified.TwoThree.Base7
import NiceCertified.TwoThree.Base8
import NiceCertified.TwoThree.Base9
import NiceCertified.TwoThree.Base11
import NiceCertified.TwoThree.Base12
import NiceCertified.TwoThree.Base13
import NiceCertified.TwoThree.Base14
import NiceCertified.TwoThree.Base15
import NiceCertified.TwoThree.Base16
import NiceCertified.TwoThree.Base17
import NiceCertified.TwoThree.Base18

/-!
# `(2,3)`: every base up to 18

Each base other than 10 has its own generated certificate module.  Base 10 is
`Nice.base_ten_nice_iff` from nice-numbers-lean, whose certificate would fail
anyway, because 69 is in its band.
-/

namespace Nice.Cert

/-- **Up to base 18, 69 in base 10 is the only `(2,3)`-nice number.** -/
theorem two_three_upto_18 {b n : Nat} (hb : 2 ≤ b) (hb' : b ≤ 18) :
    Pandigital b 2 3 n ↔ b = 10 ∧ n = 69 := by
  constructor
  · intro hp
    have : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨
        b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hp (base_2_empty_2_3 n)
    · exact absurd hp (base_3_empty_2_3 n)
    · exact absurd hp (base_4_empty_2_3 n)
    · exact absurd hp (base_5_empty_2_3 n)
    · exact absurd hp (base_6_empty_2_3 n)
    · exact absurd hp (base_7_empty_2_3 n)
    · exact absurd hp (base_8_empty_2_3 n)
    · exact absurd hp (base_9_empty_2_3 n)
    · exact ⟨rfl, base_ten_nice_iff.mp hp⟩
    · exact absurd hp (base_11_empty_2_3 n)
    · exact absurd hp (base_12_empty_2_3 n)
    · exact absurd hp (base_13_empty_2_3 n)
    · exact absurd hp (base_14_empty_2_3 n)
    · exact absurd hp (base_15_empty_2_3 n)
    · exact absurd hp (base_16_empty_2_3 n)
    · exact absurd hp (base_17_empty_2_3 n)
    · exact absurd hp (base_18_empty_2_3 n)
  · rintro ⟨rfl, rfl⟩
    exact sixtynine_pandigital

end Nice.Cert
