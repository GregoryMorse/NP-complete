module

public import ZP.Pair

@[expose] public section

/-!
# Counting certificates

`strings k` lists the bit strings of length `k`. Sums over them are sums over the numbers
`0 … 2^k - 1` (`T_range`), by way of `ofBv`, the inverse of the least-significant-bit-first
value `bv` of `ZP/Pair.lean`. Used by the P = PP machine (accept counting) and available for
other counting languages.
-/

namespace ZP

/-- Sum of `f` over all strings of length `k`. -/
def T (k : Nat) (f : List Bool → Nat) : Nat := ((strings k).map f).sum

theorem T_zero (f : List Bool → Nat) : T 0 f = f [] := by
  simp [T, strings]

theorem sum_flatMap_two (f : List Bool → Nat) (l : List (List Bool)) :
    ((l.flatMap fun c => [false :: c, true :: c]).map f).sum =
      (l.map fun c => f (false :: c) + f (true :: c)).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, Nat.add_zero]
    rw [ih]

theorem T_succ (k : Nat) (f : List Bool → Nat) :
    T (k + 1) f = T k fun c => f (false :: c) + f (true :: c) := by
  unfold T
  show (((strings k).flatMap fun c => [false :: c, true :: c]).map f).sum = _
  exact sum_flatMap_two f (strings k)

theorem T_congr (k : Nat) {f g : List Bool → Nat} (h : ∀ c, f c = g c) : T k f = T k g := by
  have : f = g := funext h
  rw [this]

theorem T_snoc : ∀ (k : Nat) (f : List Bool → Nat),
    T (k + 1) f = T k fun c => f (c ++ [false]) + f (c ++ [true])
  | 0, f => by
    rw [T_succ, T_zero, T_zero]
    simp
  | k + 1, f => by
    rw [T_succ, T_snoc k, T_succ]
    apply T_congr
    intro c
    simp only [List.cons_append]
    omega

theorem T_rev : ∀ (k : Nat) (f : List Bool → Nat), T k (fun c => f c.reverse) = T k f
  | 0, f => by simp [T_zero]
  | k + 1, f => by
    have hg := T_rev k (fun c => f (c ++ [false]) + f (c ++ [true]))
    calc T (k + 1) (fun c => f c.reverse)
        = T k (fun c => f (false :: c).reverse + f (true :: c).reverse) := T_succ k _
      _ = T k (fun c => (fun c => f (c ++ [false]) + f (c ++ [true])) c.reverse) := by
          apply T_congr
          intro c
          simp [List.reverse_cons]
      _ = T k (fun c => f (c ++ [false]) + f (c ++ [true])) := hg
      _ = T (k + 1) f := (T_snoc k f).symm

/-- The `k` bits of `v`, least significant first. -/
def ofBv : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, v => decide (v % 2 = 1) :: ofBv k (v / 2)

theorem length_ofBv : ∀ k v, (ofBv k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [ofBv, length_ofBv k]

theorem ofBv_bv : ∀ cl : List Bool, ofBv cl.length (bv cl) = cl
  | [] => rfl
  | b :: l => by
    have ih := ofBv_bv l
    have hb := bitN_le b
    show decide ((bitN b + 2 * bv l) % 2 = 1) :: ofBv l.length ((bitN b + 2 * bv l) / 2) = b :: l
    have e1 : (bitN b + 2 * bv l) / 2 = bv l := by omega
    rw [e1, ih]
    cases b <;> simp [bitN]

theorem sum_range_two (g : Nat → Nat) : ∀ m,
    ((List.range (2 * m)).map g).sum = ((List.range m).map fun u => g (2 * u) + g (2 * u + 1)).sum
  | 0 => rfl
  | m + 1 => by
    have ih := sum_range_two g m
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    simp only [List.range_succ (n := 2 * m + 1), List.range_succ (n := 2 * m), List.range_succ (n := m),
      List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
      Nat.add_zero]
    rw [ih]
    omega

theorem T_range : ∀ (k : Nat) (f : List Bool → Nat),
    T k f = ((List.range (2 ^ k)).map fun v => f (ofBv k v)).sum
  | 0, f => by simp [T_zero, ofBv]
  | k + 1, f => by
    rw [T_succ, T_range k, Nat.pow_succ, Nat.mul_comm, sum_range_two]
    apply congrArg
    apply List.map_congr_left
    intro u _
    have h1 : ¬ (2 * u) % 2 = 1 := by omega
    have h2 : (2 * u + 1) % 2 = 1 := by omega
    have h3 : 2 * u / 2 = u := by omega
    have h4 : (2 * u + 1) / 2 = u := by omega
    simp [ofBv, h2, h3, h4]

/-- Prefix sums. -/
def psum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | N + 1 => psum g N + g (N + 1)

theorem sum_range_psum (g : Nat → Nat) : ∀ N, ((List.range (N + 1)).map g).sum = psum g N
  | 0 => by simp [psum]
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_psum g N]
    simp [psum]

theorem psum_ge (g : Nat → Nat) (N : Nat) : g N ≤ psum g N := by
  cases N <;> simp [psum] <;> omega

end ZP
