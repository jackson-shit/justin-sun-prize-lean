import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-- A natural number is *powerful* if every prime dividing it divides it
with multiplicity at least two. Mathlib has no number-theoretic notion of
powerful numbers, so we define it here. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- 12167 = 23³ is powerful: its only prime divisor is 23. -/
theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdvd
  have e : (12167 : ℕ) = 23 ^ 3 := by norm_num
  rw [e] at hdvd
  have hp23 : p ∣ 23 := hp.dvd_of_dvd_pow hdvd
  have hpeq : p = 23 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp23
  subst hpeq
  rw [e]
  decide

/-- 12168 = 2³ × 3² × 13² is powerful: its only prime divisors are 2, 3, 13,
and the square of each divides 12168. -/
theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdvd
  have e : (12168 : ℕ) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  rw [e] at hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · rcases hp.dvd_mul.mp h with h2 | h3
    · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
      have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp2
      subst hpeq
      decide
    · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
      have hpeq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp3
      subst hpeq
      decide
  · have hp13 : p ∣ 13 := hp.dvd_of_dvd_pow h
    have hpeq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp13
    subst hpeq
    decide

/-- 12167 is not a square: it lies strictly between 110² and 111². -/
theorem not_isSquare_12167 : ¬ IsSquare 12167 := by
  rintro ⟨r, hr⟩
  have h110 : 110 < r := by
    by_contra hc
    push_neg at hc
    have hle : r * r ≤ 110 * 110 := Nat.mul_le_mul hc hc
    rw [← hr] at hle
    norm_num at hle
  have h111 : r < 111 := by
    by_contra hc
    push_neg at hc
    have hle : 111 * 111 ≤ r * r := Nat.mul_le_mul hc hc
    rw [← hr] at hle
    norm_num at hle
  omega

/-- 12168 is not a square: it lies strictly between 110² and 111². -/
theorem not_isSquare_12168 : ¬ IsSquare 12168 := by
  rintro ⟨r, hr⟩
  have h110 : 110 < r := by
    by_contra hc
    push_neg at hc
    have hle : r * r ≤ 110 * 110 := Nat.mul_le_mul hc hc
    rw [← hr] at hle
    norm_num at hle
  have h111 : r < 111 := by
    by_contra hc
    push_neg at hc
    have hle : 111 * 111 ≤ r * r := Nat.mul_le_mul hc hc
    rw [← hr] at hle
    norm_num at hle
  omega

/-- JSP-000301 (yes/no scope only, not the Erdős #365 counting problem):
it is false that every nonzero powerful number is followed by a powerful
number with one of the pair a square. The counterexample is Golomb's
(1970) pair 12167 = 23³ and 12168 = 2³ × 3² × 13², both powerful and
neither a square. -/
theorem jsp000301 :
    ¬ ∀ m : ℕ, m ≠ 0 → Powerful m → Powerful (m + 1) →
      IsSquare m ∨ IsSquare (m + 1) := by
  intro h
  have hp2 : Powerful (12167 + 1) := powerful_12168
  obtain hsq := h 12167 (by norm_num) powerful_12167 hp2
  rcases hsq with h1 | h2
  · exact not_isSquare_12167 h1
  · have h2' : IsSquare 12168 := h2
    exact not_isSquare_12168 h2'
