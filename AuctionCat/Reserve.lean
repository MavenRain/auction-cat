import AuctionCat.FirstPrice
import AuctionCat.SecondPrice

/-!
# AuctionCat.Reserve

Reserve-price variants of first-price and second-price sealed-bid
auctions.

A reserve price `r : Fin n` is the minimum acceptable bid.  Bids
below `r` do not win and pay nothing.  The allocation rule remains
"highest bid wins, ties to bidder 1", but conditioned on the bid
meeting the reserve.  The payment rule depends on the format:

  fpsbReserve  : winner pays own bid       (must be ≥ r)
  spsbReserve  : winner pays max(r, second-highest bid)

If no bid meets the reserve, neither bidder wins and both pay 0.
-/

set_option autoImplicit false

open CompCatTheory
open Category Functor MonoidalCategory
open MarkovCat.FinStoch

namespace AuctionCat

universe u v

/-- Underlying allocation+payment function for two-bidder first-price
    sealed-bid with reserve price `r`. -/
def fpsbReserveFn (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    Fin ((2 * n) * (2 * n)) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_left hnn
  let b1  := Fin.first i
  let b2  := Fin.second i
  let win1 := b1.val ≥ b2.val ∧ b1.val ≥ r.val
  let win2 := ¬win1 ∧ b2.val ≥ r.val
  let a1 : Fin 2 := if win1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if win2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let p1 : Fin n := if win1 then b1 else ⟨0, hn⟩
  let p2 : Fin n := if win2 then b2 else ⟨0, hn⟩
  Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)

/-- First-price sealed-bid with reserve price `r`. -/
def fpsbReserve (n : Nat) (r : Fin n) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  detMatrix (fpsbReserveFn n r)

/-- Underlying allocation+payment function for two-bidder second-price
    sealed-bid with reserve price `r`.  Winner pays `max(r, loser's bid)`. -/
def spsbReserveFn (n : Nat) (r : Fin n) (i : Fin (n * n)) :
    Fin ((2 * n) * (2 * n)) :=
  let hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hn  : 0 < n     := Nat.pos_of_mul_pos_left hnn
  let b1  := Fin.first i
  let b2  := Fin.second i
  let win1 := b1.val ≥ b2.val ∧ b1.val ≥ r.val
  let win2 := ¬win1 ∧ b2.val ≥ r.val
  let a1 : Fin 2 := if win1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if win2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let p1 : Fin n :=
    if win1 then
      ⟨max r.val b2.val, by
        have := r.isLt; have := b2.isLt; omega⟩
    else ⟨0, hn⟩
  let p2 : Fin n :=
    if win2 then
      ⟨max r.val b1.val, by
        have := r.isLt; have := b1.isLt; omega⟩
    else ⟨0, hn⟩
  Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)

/-- Second-price sealed-bid (Vickrey) with reserve price `r`. -/
def spsbReserve (n : Nat) (r : Fin n) :
    StochasticMatrix (n * n) ((2 * n) * (2 * n)) :=
  detMatrix (spsbReserveFn n r)

/-- **Allocation rule** of spsbReserve.  Bidder 1 wins iff `b1 ≥ b2`
    AND `b1 ≥ r` (clears reserve).  Two regimes: standard allocation
    when reserve clears, no allocation otherwise. -/
theorem spsbReserve_bidder1_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin (n * n)) :
    (Fin.first (Fin.first (spsbReserveFn n r i))).val = 1
    ↔ (Fin.first i).val ≥ (Fin.second i).val
      ∧ (Fin.first i).val ≥ r.val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
              ∧ (Fin.first i).val ≥ r.val
  · simp [h]
  · simp [h]

/-- **Allocation rule** of fpsbReserve.  Same as spsbReserve: bidder 1
    wins iff `b1 ≥ b2` AND `b1 ≥ r`.  Identical allocation across
    both reserve formats; they differ only in pricing. -/
theorem fpsbReserve_bidder1_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin (n * n)) :
    (Fin.first (Fin.first (fpsbReserveFn n r i))).val = 1
    ↔ (Fin.first i).val ≥ (Fin.second i).val
      ∧ (Fin.first i).val ≥ r.val := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
              ∧ (Fin.first i).val ≥ r.val
  · simp [h]
  · simp [h]

/-- **No allocation below reserve** in spsbReserve.  When both bids
    fall strictly below the reserve, neither bidder is allocated the
    item (a1 = a2 = 0).  This is the "exclusion regime" of reserve
    auctions. -/
theorem spsbReserve_no_allocation_below_reserve (n : Nat) (r : Fin n)
    (i : Fin (n * n))
    (h : (Fin.first i).val < r.val ∧ (Fin.second i).val < r.val) :
    (Fin.first (Fin.first (spsbReserveFn n r i))).val = 0
    ∧ (Fin.first (Fin.second (spsbReserveFn n r i))).val = 0 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  obtain ⟨h1, h2'⟩ := h
  constructor
  · have h_neg : ¬ ((Fin.first i).val ≥ (Fin.second i).val
                   ∧ (Fin.first i).val ≥ r.val) := by
      intro ⟨_, hr⟩
      omega
    simp [h_neg]
  · have h_neg1 : ¬ ((Fin.first i).val ≥ (Fin.second i).val
                    ∧ (Fin.first i).val ≥ r.val) := by
      intro ⟨_, hr⟩
      omega
    have h_neg2 : ¬ (Fin.second i).val ≥ r.val := by omega
    simp [h_neg1, h_neg2]

/-- **No allocation below reserve** in fpsbReserve.  Same as
    spsbReserve. -/
theorem fpsbReserve_no_allocation_below_reserve (n : Nat) (r : Fin n)
    (i : Fin (n * n))
    (h : (Fin.first i).val < r.val ∧ (Fin.second i).val < r.val) :
    (Fin.first (Fin.first (fpsbReserveFn n r i))).val = 0
    ∧ (Fin.first (Fin.second (fpsbReserveFn n r i))).val = 0 := by
  have hnn : 0 < n * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hn  : 0 < n := Nat.pos_of_mul_pos_left hnn
  have h2  : 0 < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsbReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  obtain ⟨h1, h2'⟩ := h
  constructor
  · have h_neg : ¬ ((Fin.first i).val ≥ (Fin.second i).val
                   ∧ (Fin.first i).val ≥ r.val) := by
      intro ⟨_, hr⟩
      omega
    simp [h_neg]
  · have h_neg1 : ¬ ((Fin.first i).val ≥ (Fin.second i).val
                    ∧ (Fin.first i).val ≥ r.val) := by
      intro ⟨_, hr⟩
      omega
    have h_neg2 : ¬ (Fin.second i).val ≥ r.val := by omega
    simp [h_neg1, h_neg2]

/-- Underlying allocation+payment function for three-bidder second-price
    sealed-bid with reserve price `r`.  Winner pays
    `max r (second-highest others' bid)`. -/
def spsb3ReserveFn (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    Fin ((2 * n) * (2 * n) * (2 * n)) :=
  let hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hnn  : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  let hn   : 0 < n     := Nat.pos_of_mul_pos_right hnn
  let b1   := Fin.first (Fin.first i)
  let b2   := Fin.second (Fin.first i)
  let b3   := Fin.second i
  let win1 := b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ r.val
  let win2 := ¬win1 ∧ b2.val ≥ b3.val ∧ b2.val ≥ r.val
  let win3 := ¬win1 ∧ ¬win2 ∧ b3.val ≥ r.val
  let a1 : Fin 2 := if win1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if win2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a3 : Fin 2 := if win3 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let p1 : Fin n :=
    if win1 then ⟨max r.val (max b2.val b3.val), by
      have := r.isLt; have := b2.isLt; have := b3.isLt; omega⟩
    else ⟨0, hn⟩
  let p2 : Fin n :=
    if win2 then ⟨max r.val (max b1.val b3.val), by
      have := r.isLt; have := b1.isLt; have := b3.isLt; omega⟩
    else ⟨0, hn⟩
  let p3 : Fin n :=
    if win3 then ⟨max r.val (max b1.val b2.val), by
      have := r.isLt; have := b1.isLt; have := b2.isLt; omega⟩
    else ⟨0, hn⟩
  Fin.pair (Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)) (Fin.pair a3 p3)

/-- Three-bidder Vickrey auction with reserve price `r`. -/
def spsb3Reserve (n : Nat) (r : Fin n) :
    StochasticMatrix ((n * n) * n) ((2 * n) * (2 * n) * (2 * n)) :=
  detMatrix (spsb3ReserveFn n r)

/-- Underlying allocation+payment function for three-bidder first-price
    sealed-bid with reserve price `r`. -/
def fpsb3ReserveFn (n : Nat) (r : Fin n) (i : Fin ((n * n) * n)) :
    Fin ((2 * n) * (2 * n) * (2 * n)) :=
  let hnnn : 0 < (n * n) * n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let hnn  : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  let hn   : 0 < n     := Nat.pos_of_mul_pos_right hnn
  let b1   := Fin.first (Fin.first i)
  let b2   := Fin.second (Fin.first i)
  let b3   := Fin.second i
  let win1 := b1.val ≥ b2.val ∧ b1.val ≥ b3.val ∧ b1.val ≥ r.val
  let win2 := ¬win1 ∧ b2.val ≥ b3.val ∧ b2.val ≥ r.val
  let win3 := ¬win1 ∧ ¬win2 ∧ b3.val ≥ r.val
  let a1 : Fin 2 := if win1 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a2 : Fin 2 := if win2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let a3 : Fin 2 := if win3 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let p1 : Fin n := if win1 then b1 else ⟨0, hn⟩
  let p2 : Fin n := if win2 then b2 else ⟨0, hn⟩
  let p3 : Fin n := if win3 then b3 else ⟨0, hn⟩
  Fin.pair (Fin.pair (Fin.pair a1 p1) (Fin.pair a2 p2)) (Fin.pair a3 p3)

/-- Three-bidder first-price sealed-bid with reserve price `r`. -/
def fpsb3Reserve (n : Nat) (r : Fin n) :
    StochasticMatrix ((n * n) * n) ((2 * n) * (2 * n) * (2 * n)) :=
  detMatrix (fpsb3ReserveFn n r)

/-- **Allocation rule** of spsb3Reserve.  Bidder 1 wins iff
    `b1 ≥ b2 ∧ b1 ≥ b3 ∧ b1 ≥ r`. -/
theorem spsb3Reserve_bidder1_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.first (Fin.first (spsb3ReserveFn n r i)))).val = 1
    ↔ (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.first (Fin.first i)).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
              ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
              ∧ (Fin.first (Fin.first i)).val ≥ r.val
  · simp [h]
  · simp [h]

/-- **Allocation rule** of fpsb3Reserve.  Same as spsb3Reserve. -/
theorem fpsb3Reserve_bidder1_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.first (Fin.first (fpsb3ReserveFn n r i)))).val = 1
    ↔ (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
      ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.first (Fin.first i)).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases h : (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
              ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
              ∧ (Fin.first (Fin.first i)).val ≥ r.val
  · simp [h]
  · simp [h]

/-- **No allocation below reserve** in spsb3Reserve.  When all three
    bids fall strictly below the reserve, none of the bidders is
    allocated (a1 = a2 = a3 = 0). -/
theorem spsb3Reserve_no_allocation_below_reserve (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n))
    (h : (Fin.first (Fin.first i)).val < r.val
        ∧ (Fin.second (Fin.first i)).val < r.val
        ∧ (Fin.second i).val < r.val) :
    (Fin.first (Fin.first (Fin.first (spsb3ReserveFn n r i)))).val = 0
    ∧ (Fin.first (Fin.second (Fin.first (spsb3ReserveFn n r i)))).val = 0
    ∧ (Fin.first (Fin.second (spsb3ReserveFn n r i))).val = 0 := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  obtain ⟨hb1, hb2, hb3⟩ := h
  have h_neg_w1 : ¬ ((Fin.first (Fin.first i)).val
                      ≥ (Fin.second (Fin.first i)).val
                    ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
                    ∧ (Fin.first (Fin.first i)).val ≥ r.val) := by
    intro ⟨_, _, hr⟩
    omega
  have h_neg_w2 : ¬ ((Fin.second (Fin.first i)).val ≥ (Fin.second i).val
                    ∧ (Fin.second (Fin.first i)).val ≥ r.val) := by
    intro ⟨_, hr⟩
    omega
  have h_neg_w3 : ¬ (Fin.second i).val ≥ r.val := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [h_neg_w1]
  · simp [h_neg_w1, h_neg_w2]
  · simp [h_neg_w1, h_neg_w2, h_neg_w3]

/-- **No allocation below reserve** in fpsb3Reserve.  Same as
    spsb3Reserve. -/
theorem fpsb3Reserve_no_allocation_below_reserve (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n))
    (h : (Fin.first (Fin.first i)).val < r.val
        ∧ (Fin.second (Fin.first i)).val < r.val
        ∧ (Fin.second i).val < r.val) :
    (Fin.first (Fin.first (Fin.first (fpsb3ReserveFn n r i)))).val = 0
    ∧ (Fin.first (Fin.second (Fin.first (fpsb3ReserveFn n r i)))).val = 0
    ∧ (Fin.first (Fin.second (fpsb3ReserveFn n r i))).val = 0 := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  obtain ⟨hb1, hb2, hb3⟩ := h
  have h_neg_w1 : ¬ ((Fin.first (Fin.first i)).val
                      ≥ (Fin.second (Fin.first i)).val
                    ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
                    ∧ (Fin.first (Fin.first i)).val ≥ r.val) := by
    intro ⟨_, _, hr⟩
    omega
  have h_neg_w2 : ¬ ((Fin.second (Fin.first i)).val ≥ (Fin.second i).val
                    ∧ (Fin.second (Fin.first i)).val ≥ r.val) := by
    intro ⟨_, hr⟩
    omega
  have h_neg_w3 : ¬ (Fin.second i).val ≥ r.val := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [h_neg_w1]
  · simp [h_neg_w1, h_neg_w2]
  · simp [h_neg_w1, h_neg_w2, h_neg_w3]

/-- **fpsbReserve and spsbReserve have IDENTICAL allocation rules**:
    bidder 1's allocation under fpsbReserveFn equals bidder 1's
    allocation under spsbReserveFn at every joint bid.  Same as the
    no-reserve case (both formats differ only in pricing). -/
theorem fpsbReserve_spsbReserve_same_allocation (n : Nat) (r : Fin n)
    (i : Fin (n * n)) :
    (Fin.first (Fin.first (fpsbReserveFn n r i))).val
    = (Fin.first (Fin.first (spsbReserveFn n r i))).val := by
  by_cases h : (Fin.first i).val ≥ (Fin.second i).val
              ∧ (Fin.first i).val ≥ r.val
  · rw [(fpsbReserve_bidder1_allocated_iff_winner n r i).mpr h,
        (spsbReserve_bidder1_allocated_iff_winner n r i).mpr h]
  · have h_fpsb : (Fin.first (Fin.first (fpsbReserveFn n r i))).val ≠ 1 := by
      intro hcontra
      exact h ((fpsbReserve_bidder1_allocated_iff_winner n r i).mp hcontra)
    have h_spsb : (Fin.first (Fin.first (spsbReserveFn n r i))).val ≠ 1 := by
      intro hcontra
      exact h ((spsbReserve_bidder1_allocated_iff_winner n r i).mp hcontra)
    have hb1 := (Fin.first (Fin.first (fpsbReserveFn n r i))).isLt
    have hb2 := (Fin.first (Fin.first (spsbReserveFn n r i))).isLt
    omega

/-- **fpsb3Reserve and spsb3Reserve have IDENTICAL allocation rules**.
    Same as the 2-bidder reserve case. -/
theorem fpsb3Reserve_spsb3Reserve_same_allocation (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.first (Fin.first (fpsb3ReserveFn n r i)))).val
    = (Fin.first (Fin.first (Fin.first (spsb3ReserveFn n r i)))).val := by
  by_cases h : (Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
              ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
              ∧ (Fin.first (Fin.first i)).val ≥ r.val
  · rw [(fpsb3Reserve_bidder1_allocated_iff_winner n r i).mpr h,
        (spsb3Reserve_bidder1_allocated_iff_winner n r i).mpr h]
  · have h_fpsb : (Fin.first (Fin.first (Fin.first
                  (fpsb3ReserveFn n r i)))).val ≠ 1 := by
      intro hcontra
      exact h ((fpsb3Reserve_bidder1_allocated_iff_winner n r i).mp hcontra)
    have h_spsb : (Fin.first (Fin.first (Fin.first
                  (spsb3ReserveFn n r i)))).val ≠ 1 := by
      intro hcontra
      exact h ((spsb3Reserve_bidder1_allocated_iff_winner n r i).mp hcontra)
    have hb1 := (Fin.first (Fin.first (Fin.first
                  (fpsb3ReserveFn n r i)))).isLt
    have hb2 := (Fin.first (Fin.first (Fin.first
                  (spsb3ReserveFn n r i)))).isLt
    omega

/-- Bidder 2's spsb3Reserve allocation: bidder 2 wins iff `¬win1 ∧
    b2 ≥ b3 ∧ b2 ≥ r`. -/
theorem spsb3Reserve_bidder2_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.second (Fin.first (spsb3ReserveFn n r i)))).val = 1
    ↔ ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.second (Fin.first i)).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw2 :
      ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.second (Fin.first i)).val ≥ r.val
  · simp [hw2]
  · simp [hw2]

/-- Bidder 2's fpsb3Reserve allocation: same condition as spsb3Reserve
    (formats differ only in pricing, not allocation). -/
theorem fpsb3Reserve_bidder2_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.second (Fin.first (fpsb3ReserveFn n r i)))).val = 1
    ↔ ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.second (Fin.first i)).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw2 :
      ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
      ∧ (Fin.second (Fin.first i)).val ≥ r.val
  · simp [hw2]
  · simp [hw2]

/-- Bidder 3's spsb3Reserve allocation: bidder 3 wins iff `¬win1 ∧
    ¬win2 ∧ b3 ≥ r`. -/
theorem spsb3Reserve_bidder3_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.second (spsb3ReserveFn n r i))).val = 1
    ↔ ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ ¬(¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
            ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
            ∧ (Fin.first (Fin.first i)).val ≥ r.val)
          ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
          ∧ (Fin.second (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second i).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold spsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw3 :
      ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ ¬(¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
            ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
            ∧ (Fin.first (Fin.first i)).val ≥ r.val)
          ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
          ∧ (Fin.second (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second i).val ≥ r.val
  · simp [hw3]
  · simp [hw3]

/-- Bidder 3's fpsb3Reserve allocation: same condition as spsb3Reserve. -/
theorem fpsb3Reserve_bidder3_allocated_iff_winner (n : Nat) (r : Fin n)
    (i : Fin ((n * n) * n)) :
    (Fin.first (Fin.second (fpsb3ReserveFn n r i))).val = 1
    ↔ ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ ¬(¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
            ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
            ∧ (Fin.first (Fin.first i)).val ≥ r.val)
          ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
          ∧ (Fin.second (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second i).val ≥ r.val := by
  have hnnn : 0 < (n * n) * n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hnn : 0 < n * n := Nat.pos_of_mul_pos_right hnnn
  have hn  : 0 < n := Nat.pos_of_mul_pos_right hnn
  have h2  : (0 : Nat) < 2 := by decide
  have h2n : 0 < 2 * n := by omega
  unfold fpsb3ReserveFn
  simp only [Fin.first_pair, Fin.second_pair h2n, Fin.second_pair h2,
             Fin.first_val, Fin.second_val]
  by_cases hw3 :
      ¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
        ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
        ∧ (Fin.first (Fin.first i)).val ≥ r.val)
      ∧ ¬(¬((Fin.first (Fin.first i)).val ≥ (Fin.second (Fin.first i)).val
            ∧ (Fin.first (Fin.first i)).val ≥ (Fin.second i).val
            ∧ (Fin.first (Fin.first i)).val ≥ r.val)
          ∧ (Fin.second (Fin.first i)).val ≥ (Fin.second i).val
          ∧ (Fin.second (Fin.first i)).val ≥ r.val)
      ∧ (Fin.second i).val ≥ r.val
  · simp [hw3]
  · simp [hw3]

end AuctionCat
