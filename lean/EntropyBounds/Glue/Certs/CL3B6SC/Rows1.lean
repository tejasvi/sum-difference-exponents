import EntropyBounds.Glue.Certs.CL3B6SC.Ids0
import EntropyBounds.Glue.Certs.CL3B6SC.Ids1
import EntropyBounds.Glue.Certs.CL3B6SC.Ids2
import EntropyBounds.Glue.Certs.CL3B6SC.Ids3
import EntropyBounds.Glue.Certs.CL3B6SC.Ids4
import EntropyBounds.Glue.Certs.CL3B6SC.Lemmas
import EntropyBounds.Glue.Lemma

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.Glue.Certs.CL3B6SC

open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences SumsDifferences.NonShannon
open EntropyBounds.Lem

theorem row150 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L46 + (1 : ℝ) * (CF Γ p).H L127 + (-1 : ℝ) * (CF Γ p).H L621 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L72 [F5]
  rw [show [F43] ++ L72 ++ [F5] = L622 from rfl, show [F43] ++ L72 = L616 from rfl,
    show L72 ++ [F5] = L620 from rfl] at hh
  rw [i340 h, i336 h, i339 h, i35 h] at hh
  linarith

theorem row151 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L46 + (1 : ℝ) * (CF Γ p).H L623 + (-1 : ℝ) * (CF Γ p).H L625 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L72 [F93]
  rw [show [F43] ++ L72 ++ [F93] = L626 from rfl, show [F43] ++ L72 = L616 from rfl,
    show L72 ++ [F93] = L624 from rfl] at hh
  rw [i342 h, i336 h, i341 h, i35 h] at hh
  linarith

theorem row152 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L46 + (1 : ℝ) * (CF Γ p).H L627 + (-1 : ℝ) * (CF Γ p).H L629 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L72 [F69]
  rw [show [F43] ++ L72 ++ [F69] = L630 from rfl, show [F43] ++ L72 = L616 from rfl,
    show L72 ++ [F69] = L628 from rfl] at hh
  rw [i344 h, i336 h, i343 h, i35 h] at hh
  linarith

theorem row153 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L621 + (1 : ℝ) * (CF Γ p).H L633 + (-1 : ℝ) * (CF Γ p).H L636 + (-1 : ℝ) * (CF Γ p).H L362 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L363 [F30]
  rw [show [F43] ++ L363 ++ [F30] = L637 from rfl, show [F43] ++ L363 = L631 from rfl,
    show L363 ++ [F30] = L634 from rfl] at hh
  rw [i347 h, i345 h, i346 h, i180 h] at hh
  linarith

theorem row154 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L188 + (1 : ℝ) * (CF Γ p).H L95 + (-1 : ℝ) * (CF Γ p).H L641 + (-1 : ℝ) * (CF Γ p).H L213 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L214 [F30]
  rw [show [F43] ++ L214 ++ [F30] = L642 from rfl, show [F43] ++ L214 = L639 from rfl,
    show L214 ++ [F30] = L640 from rfl] at hh
  rw [i350 h, i348 h, i349 h, i104 h] at hh
  linarith

theorem row155 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L643 + (1 : ℝ) * (CF Γ p).H L113 + (-1 : ℝ) * (CF Γ p).H L645 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L76 [F34]
  rw [show [F43] ++ L76 ++ [F34] = L646 from rfl, show [F43] ++ L76 = L644 from rfl,
    show L76 ++ [F34] = L378 from rfl] at hh
  rw [i352 h, i351 h, i190 h, i37 h] at hh
  linarith

theorem row156 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L211 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L649 + (-1 : ℝ) * (CF Γ p).H L91 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L92 [F37]
  rw [show [F43] ++ L92 ++ [F37] = L650 from rfl, show [F43] ++ L92 = L647 from rfl,
    show L92 ++ [F37] = L648 from rfl] at hh
  rw [i355 h, i353 h, i354 h, i45 h] at hh
  linarith

theorem row157 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L408 + (1 : ℝ) * (CF Γ p).H L265 + (-1 : ℝ) * (CF Γ p).H L653 + (-1 : ℝ) * (CF Γ p).H L560 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L655 [F30]
  rw [show [F10] ++ L655 ++ [F30] = L654 from rfl, show [F10] ++ L655 = L651 from rfl,
    show L655 ++ [F30] = L652 from rfl] at hh
  rw [i358 h, i356 h, i357 h, i359 h] at hh
  linarith

theorem row158 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L408 + (1 : ℝ) * (CF Γ p).H L570 + (-1 : ℝ) * (CF Γ p).H L657 + (-1 : ℝ) * (CF Γ p).H L560 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L655 [F34]
  rw [show [F10] ++ L655 ++ [F34] = L658 from rfl, show [F10] ++ L655 = L651 from rfl,
    show L655 ++ [F34] = L656 from rfl] at hh
  rw [i361 h, i356 h, i360 h, i359 h] at hh
  linarith

theorem row159 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L399 + (1 : ℝ) * (CF Γ p).H L235 + (-1 : ℝ) * (CF Γ p).H L376 + (-1 : ℝ) * (CF Γ p).H L397 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L662 [F34]
  rw [show [F10] ++ L662 ++ [F34] = L661 from rfl, show [F10] ++ L662 = L659 from rfl,
    show L662 ++ [F34] = L660 from rfl] at hh
  rw [i364 h, i362 h, i363 h, i365 h] at hh
  linarith

theorem row160 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L177 + (-1 : ℝ) * (CF Γ p).H L198 + (-1 : ℝ) * (CF Γ p).H L129 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L130 [F37]
  rw [show [F30] ++ L130 ++ [F37] = L665 from rfl, show [F30] ++ L130 = L663 from rfl,
    show L130 ++ [F37] = L664 from rfl] at hh
  rw [i368 h, i366 h, i367 h, i64 h] at hh
  linarith

theorem row161 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L135 + (-1 : ℝ) * (CF Γ p).H L633 + (-1 : ℝ) * (CF Γ p).H L196 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L197 [F5]
  rw [show [F30] ++ L197 ++ [F5] = L667 from rfl, show [F30] ++ L197 = L666 from rfl,
    show L197 ++ [F5] = L572 from rfl] at hh
  rw [i370 h, i369 h, i309 h, i96 h] at hh
  linarith

theorem row162 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L282 + (1 : ℝ) * (CF Γ p).H L669 + (-1 : ℝ) * (CF Γ p).H L671 + (-1 : ℝ) * (CF Γ p).H L157 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L158 [F5]
  rw [show [F30] ++ L158 ++ [F5] = L672 from rfl, show [F30] ++ L158 = L668 from rfl,
    show L158 ++ [F5] = L670 from rfl] at hh
  rw [i373 h, i371 h, i372 h, i77 h] at hh
  linarith

theorem row163 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L198 + (1 : ℝ) * (CF Γ p).H L356 + (-1 : ℝ) * (CF Γ p).H L516 + (-1 : ℝ) * (CF Γ p).H L338 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L676 [F41]
  rw [show [F7] ++ L676 ++ [F41] = L675 from rfl, show [F7] ++ L676 = L673 from rfl,
    show L676 ++ [F41] = L674 from rfl] at hh
  rw [i376 h, i374 h, i375 h, i377 h] at hh
  linarith

theorem row164 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L81 + (1 : ℝ) * (CF Γ p).H L194 + (-1 : ℝ) * (CF Γ p).H L679 + (-1 : ℝ) * (CF Γ p).H L181 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L182 [F38]
  rw [show [F30] ++ L182 ++ [F38] = L680 from rfl, show [F30] ++ L182 = L677 from rfl,
    show L182 ++ [F38] = L678 from rfl] at hh
  rw [i380 h, i378 h, i379 h, i89 h] at hh
  linarith

theorem row165 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L85 + (1 : ℝ) * (CF Γ p).H L175 + (-1 : ℝ) * (CF Γ p).H L224 + (-1 : ℝ) * (CF Γ p).H L263 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L264 [F34]
  rw [show [F30] ++ L264 ++ [F34] = L683 from rfl, show [F30] ++ L264 = L681 from rfl,
    show L264 ++ [F34] = L682 from rfl] at hh
  rw [i383 h, i381 h, i382 h, i126 h] at hh
  linarith

theorem row166 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L592 + (1 : ℝ) * (CF Γ p).H L685 + (-1 : ℝ) * (CF Γ p).H L687 + (-1 : ℝ) * (CF Γ p).H L209 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L210 [F93]
  rw [show [F34] ++ L210 ++ [F93] = L688 from rfl, show [F34] ++ L210 = L684 from rfl,
    show L210 ++ [F93] = L686 from rfl] at hh
  rw [i386 h, i384 h, i385 h, i102 h] at hh
  linarith

theorem row167 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L113 + (1 : ℝ) * (CF Γ p).H L250 + (-1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L76 [F31]
  rw [show [F34] ++ L76 ++ [F31] = L691 from rfl, show [F34] ++ L76 = L689 from rfl,
    show L76 ++ [F31] = L690 from rfl] at hh
  rw [i389 h, i387 h, i388 h, i37 h] at hh
  linarith

theorem row168 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L113 + (1 : ℝ) * (CF Γ p).H L692 + (-1 : ℝ) * (CF Γ p).H L606 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L76 [F38]
  rw [show [F34] ++ L76 ++ [F38] = L694 from rfl, show [F34] ++ L76 = L689 from rfl,
    show L76 ++ [F38] = L693 from rfl] at hh
  rw [i391 h, i387 h, i390 h, i37 h] at hh
  linarith

theorem row169 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L113 + (1 : ℝ) * (CF Γ p).H L695 + (-1 : ℝ) * (CF Γ p).H L311 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L76 [F14]
  rw [show [F34] ++ L76 ++ [F14] = L697 from rfl, show [F34] ++ L76 = L689 from rfl,
    show L76 ++ [F14] = L696 from rfl] at hh
  rw [i393 h, i387 h, i392 h, i37 h] at hh
  linarith

theorem row170 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L277 + (1 : ℝ) * (CF Γ p).H L235 + (-1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L592 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L593 [F7]
  rw [show [F41] ++ L593 ++ [F7] = L701 from rfl, show [F41] ++ L593 = L699 from rfl,
    show L593 ++ [F7] = L700 from rfl] at hh
  rw [i396 h, i394 h, i395 h, i323 h] at hh
  linarith

theorem row171 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L235 + (1 : ℝ) * (CF Γ p).H L265 + (-1 : ℝ) * (CF Γ p).H L537 + (-1 : ℝ) * (CF Γ p).H L397 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L662 [F30]
  rw [show [F34] ++ L662 ++ [F30] = L704 from rfl, show [F34] ++ L662 = L702 from rfl,
    show L662 ++ [F30] = L703 from rfl] at hh
  rw [i399 h, i397 h, i398 h, i365 h] at hh
  linarith

theorem row172 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L235 + (1 : ℝ) * (CF Γ p).H L706 + (-1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L709 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L710 [F41]
  rw [show [F7] ++ L710 ++ [F41] = L708 from rfl, show [F7] ++ L710 = L705 from rfl,
    show L710 ++ [F41] = L707 from rfl] at hh
  rw [i402 h, i400 h, i401 h, i403 h] at hh
  linarith

theorem row173 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L190 + (1 : ℝ) * (CF Γ p).H L712 + (-1 : ℝ) * (CF Γ p).H L714 + (-1 : ℝ) * (CF Γ p).H L196 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L197 [F80]
  rw [show [F34] ++ L197 ++ [F80] = L715 from rfl, show [F34] ++ L197 = L711 from rfl,
    show L197 ++ [F80] = L713 from rfl] at hh
  rw [i406 h, i404 h, i405 h, i96 h] at hh
  linarith

theorem row174 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L716 + (1 : ℝ) * (CF Γ p).H L203 + (-1 : ℝ) * (CF Γ p).H L718 + (-1 : ℝ) * (CF Γ p).H L147 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L148 [F38]
  rw [show [F34] ++ L148 ++ [F38] = L719 from rfl, show [F34] ++ L148 = L717 from rfl,
    show L148 ++ [F38] = L460 from rfl] at hh
  rw [i408 h, i407 h, i240 h, i73 h] at hh
  linarith

theorem row175 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L383 + (1 : ℝ) * (CF Γ p).H L338 + (-1 : ℝ) * (CF Γ p).H L722 + (-1 : ℝ) * (CF Γ p).H L157 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L158 [F37]
  rw [show [F34] ++ L158 ++ [F37] = L723 from rfl, show [F34] ++ L158 = L720 from rfl,
    show L158 ++ [F37] = L721 from rfl] at hh
  rw [i411 h, i409 h, i410 h, i77 h] at hh
  linarith

theorem row176 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L724 + (1 : ℝ) * (CF Γ p).H L192 + (-1 : ℝ) * (CF Γ p).H L537 + (-1 : ℝ) * (CF Γ p).H L222 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L223 [F37]
  rw [show [F34] ++ L223 ++ [F37] = L727 from rfl, show [F34] ++ L223 = L725 from rfl,
    show L223 ++ [F37] = L726 from rfl] at hh
  rw [i414 h, i412 h, i413 h, i108 h] at hh
  linarith

theorem row177 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L231 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L729 + (-1 : ℝ) * (CF Γ p).H L97 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] L98 [F37]
  rw [show [F34] ++ L98 ++ [F37] = L730 from rfl, show [F34] ++ L98 = L232 from rfl,
    show L98 ++ [F37] = L478 from rfl] at hh
  rw [i415 h, i112 h, i251 h, i48 h] at hh
  linarith

theorem row178 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L149 + (1 : ℝ) * (CF Γ p).H L242 + (-1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L240 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L241 [F7]
  rw [show [F6] ++ L241 ++ [F7] = L733 from rfl, show [F6] ++ L241 = L731 from rfl,
    show L241 ++ [F7] = L732 from rfl] at hh
  rw [i418 h, i416 h, i417 h, i116 h] at hh
  linarith

theorem row179 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L149 + (1 : ℝ) * (CF Γ p).H L718 + (-1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L716 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L737 [F38]
  rw [show [F6] ++ L737 ++ [F38] = L736 from rfl, show [F6] ++ L737 = L734 from rfl,
    show L737 ++ [F38] = L735 from rfl] at hh
  rw [i421 h, i419 h, i420 h, i422 h] at hh
  linarith

theorem row180 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L311 + (1 : ℝ) * (CF Γ p).H L344 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L741 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L742 [F7]
  rw [show [F6] ++ L742 ++ [F7] = L740 from rfl, show [F6] ++ L742 = L738 from rfl,
    show L742 ++ [F7] = L739 from rfl] at hh
  rw [i425 h, i423 h, i424 h, i426 h] at hh
  linarith

theorem row181 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L311 + (1 : ℝ) * (CF Γ p).H L744 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L747 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L748 [F7]
  rw [show [F10] ++ L748 ++ [F7] = L746 from rfl, show [F10] ++ L748 = L743 from rfl,
    show L748 ++ [F7] = L745 from rfl] at hh
  rw [i429 h, i427 h, i428 h, i430 h] at hh
  linarith

theorem row182 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L311 + (1 : ℝ) * (CF Γ p).H L750 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L507 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L753 [F43]
  rw [show [F10] ++ L753 ++ [F43] = L752 from rfl, show [F10] ++ L753 = L749 from rfl,
    show L753 ++ [F43] = L751 from rfl] at hh
  rw [i433 h, i431 h, i432 h, i434 h] at hh
  linarith

theorem row183 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L311 + (1 : ℝ) * (CF Γ p).H L755 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L758 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L759 [F7]
  rw [show [F10] ++ L759 ++ [F7] = L757 from rfl, show [F10] ++ L759 = L754 from rfl,
    show L759 ++ [F7] = L756 from rfl] at hh
  rw [i437 h, i435 h, i436 h, i438 h] at hh
  linarith

theorem row184 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L224 + (1 : ℝ) * (CF Γ p).H L761 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L463 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L471 [F9]
  rw [show [F30] ++ L471 ++ [F9] = L763 from rfl, show [F30] ++ L471 = L760 from rfl,
    show L471 ++ [F9] = L762 from rfl] at hh
  rw [i441 h, i439 h, i440 h, i247 h] at hh
  linarith

theorem row185 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L224 + (1 : ℝ) * (CF Γ p).H L766 + (-1 : ℝ) * (CF Γ p).H L768 + (-1 : ℝ) * (CF Γ p).H L724 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L725 [F41]
  rw [show [F6] ++ L725 ++ [F41] = L769 from rfl, show [F6] ++ L725 = L765 from rfl,
    show L725 ++ [F41] = L767 from rfl] at hh
  rw [i444 h, i442 h, i443 h, i412 h] at hh
  linarith

theorem row186 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L537 + (1 : ℝ) * (CF Γ p).H L636 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L773 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L774 [F41]
  rw [show [F6] ++ L774 ++ [F41] = L772 from rfl, show [F6] ++ L774 = L770 from rfl,
    show L774 ++ [F41] = L771 from rfl] at hh
  rw [i447 h, i445 h, i446 h, i448 h] at hh
  linarith

theorem row187 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L537 + (1 : ℝ) * (CF Γ p).H L776 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L679 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L779 [F10]
  rw [show [F6] ++ L779 ++ [F10] = L778 from rfl, show [F6] ++ L779 = L775 from rfl,
    show L779 ++ [F10] = L777 from rfl] at hh
  rw [i451 h, i449 h, i450 h, i452 h] at hh
  linarith

theorem row188 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L115 + (1 : ℝ) * (CF Γ p).H L89 + (-1 : ℝ) * (CF Γ p).H L356 + (-1 : ℝ) * (CF Γ p).H L91 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L92 [F31]
  rw [show [F37] ++ L92 ++ [F31] = L782 from rfl, show [F37] ++ L92 = L780 from rfl,
    show L92 ++ [F31] = L781 from rfl] at hh
  rw [i455 h, i453 h, i454 h, i45 h] at hh
  linarith

theorem row189 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L115 + (1 : ℝ) * (CF Γ p).H L229 + (-1 : ℝ) * (CF Γ p).H L784 + (-1 : ℝ) * (CF Γ p).H L91 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L92 [F38]
  rw [show [F37] ++ L92 ++ [F38] = L785 from rfl, show [F37] ++ L92 = L780 from rfl,
    show L92 ++ [F38] = L783 from rfl] at hh
  rw [i457 h, i453 h, i456 h, i45 h] at hh
  linarith

theorem row190 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L115 + (1 : ℝ) * (CF Γ p).H L787 + (-1 : ℝ) * (CF Γ p).H L789 + (-1 : ℝ) * (CF Γ p).H L97 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L98 [F133]
  rw [show [F37] ++ L98 ++ [F133] = L790 from rfl, show [F37] ++ L98 = L786 from rfl,
    show L98 ++ [F133] = L788 from rfl] at hh
  rw [i460 h, i458 h, i459 h, i48 h] at hh
  linarith

theorem row191 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L192 + (1 : ℝ) * (CF Γ p).H L792 + (-1 : ℝ) * (CF Γ p).H L794 + (-1 : ℝ) * (CF Γ p).H L222 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L223 [F137]
  rw [show [F37] ++ L223 ++ [F137] = L795 from rfl, show [F37] ++ L223 = L791 from rfl,
    show L223 ++ [F137] = L793 from rfl] at hh
  rw [i463 h, i461 h, i462 h, i108 h] at hh
  linarith

theorem row192 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L205 + (1 : ℝ) * (CF Γ p).H L797 + (-1 : ℝ) * (CF Γ p).H L794 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L72 [F99]
  rw [show [F37] ++ L72 ++ [F99] = L799 from rfl, show [F37] ++ L72 = L796 from rfl,
    show L72 ++ [F99] = L798 from rfl] at hh
  rw [i466 h, i464 h, i465 h, i35 h] at hh
  linarith

theorem row193 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L800 + (1 : ℝ) * (CF Γ p).H L802 + (-1 : ℝ) * (CF Γ p).H L804 + (-1 : ℝ) * (CF Γ p).H L209 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] L210 [F73]
  rw [show [F37] ++ L210 ++ [F73] = L805 from rfl, show [F37] ++ L210 = L801 from rfl,
    show L210 ++ [F73] = L803 from rfl] at hh
  rw [i469 h, i467 h, i468 h, i102 h] at hh
  linarith

theorem row194 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L242 + (1 : ℝ) * (CF Γ p).H L394 + (-1 : ℝ) * (CF Γ p).H L653 + (-1 : ℝ) * (CF Γ p).H L809 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L810 [F10]
  rw [show [F7] ++ L810 ++ [F10] = L808 from rfl, show [F7] ++ L810 = L806 from rfl,
    show L810 ++ [F10] = L807 from rfl] at hh
  rw [i472 h, i470 h, i471 h, i473 h] at hh
  linarith

theorem row195 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L242 + (1 : ℝ) * (CF Γ p).H L457 + (-1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L455 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L456 [F6]
  rw [show [F7] ++ L456 ++ [F6] = L813 from rfl, show [F7] ++ L456 = L811 from rfl,
    show L456 ++ [F6] = L812 from rfl] at hh
  rw [i476 h, i474 h, i475 h, i237 h] at hh
  linarith

theorem row196 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L265 + (1 : ℝ) * (CF Γ p).H L289 + (-1 : ℝ) * (CF Γ p).H L653 + (-1 : ℝ) * (CF Γ p).H L817 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L818 [F10]
  rw [show [F7] ++ L818 ++ [F10] = L816 from rfl, show [F7] ++ L818 = L814 from rfl,
    show L818 ++ [F10] = L815 from rfl] at hh
  rw [i479 h, i477 h, i478 h, i480 h] at hh
  linarith

theorem row197 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L250 + (1 : ℝ) * (CF Γ p).H L819 + (-1 : ℝ) * (CF Γ p).H L821 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] L118 [F93]
  rw [show [F31] ++ L118 ++ [F93] = L822 from rfl, show [F31] ++ L118 = L251 from rfl,
    show L118 ++ [F93] = L820 from rfl] at hh
  rw [i482 h, i121 h, i481 h, i58 h] at hh
  linarith

theorem row198 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L50 + (1 : ℝ) * (CF Γ p).H L824 + (-1 : ℝ) * (CF Γ p).H L599 + (-1 : ℝ) * (CF Γ p).H L213 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] L214 [F80]
  rw [show [F31] ++ L214 ++ [F80] = L826 from rfl, show [F31] ++ L214 = L823 from rfl,
    show L214 ++ [F80] = L825 from rfl] at hh
  rw [i485 h, i483 h, i484 h, i104 h] at hh
  linarith

theorem row199 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L287 + (1 : ℝ) * (CF Γ p).H L829 + (-1 : ℝ) * (CF Γ p).H L831 + (-1 : ℝ) * (CF Γ p).H L209 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L210 [F38]
  rw [show [F5] ++ L210 ++ [F38] = L832 from rfl, show [F5] ++ L210 = L828 from rfl,
    show L210 ++ [F38] = L830 from rfl] at hh
  rw [i488 h, i486 h, i487 h, i102 h] at hh
  linarith

theorem row200 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L833 + (1 : ℝ) * (CF Γ p).H L835 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L587 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L839 [F7]
  rw [show [F41] ++ L839 ++ [F7] = L837 from rfl, show [F41] ++ L839 = L834 from rfl,
    show L839 ++ [F7] = L836 from rfl] at hh
  rw [i491 h, i489 h, i490 h, i492 h] at hh
  linarith

theorem row201 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L252 + (1 : ℝ) * (CF Γ p).H L486 + (-1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L575 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] L576 [F34]
  rw [show [F31] ++ L576 ++ [F34] = L841 from rfl, show [F31] ++ L576 = L840 from rfl,
    show L576 ++ [F34] = L577 from rfl] at hh
  rw [i494 h, i493 h, i312 h, i311 h] at hh
  linarith

theorem row202 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L274 + (1 : ℝ) * (CF Γ p).H L461 + (-1 : ℝ) * (CF Γ p).H L844 + (-1 : ℝ) * (CF Γ p).H L388 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L846 [F6]
  rw [show [F7] ++ L846 ++ [F6] = L845 from rfl, show [F7] ++ L846 = L842 from rfl,
    show L846 ++ [F6] = L843 from rfl] at hh
  rw [i497 h, i495 h, i496 h, i498 h] at hh
  linarith

theorem row203 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L741 + (1 : ℝ) * (CF Γ p).H L848 + (-1 : ℝ) * (CF Γ p).H L850 + (-1 : ℝ) * (CF Γ p).H L612 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L613 [F143]
  rw [show [F10] ++ L613 ++ [F143] = L851 from rfl, show [F10] ++ L613 = L847 from rfl,
    show L613 ++ [F143] = L849 from rfl] at hh
  rw [i501 h, i499 h, i500 h, i334 h] at hh
  linarith

theorem row204 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L741 + (1 : ℝ) * (CF Γ p).H L853 + (-1 : ℝ) * (CF Γ p).H L855 + (-1 : ℝ) * (CF Γ p).H L695 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L857 [F15]
  rw [show [F10] ++ L857 ++ [F15] = L856 from rfl, show [F10] ++ L857 = L852 from rfl,
    show L857 ++ [F15] = L854 from rfl] at hh
  rw [i504 h, i502 h, i503 h, i505 h] at hh
  linarith

theorem row205 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L289 + (1 : ℝ) * (CF Γ p).H L390 + (-1 : ℝ) * (CF Γ p).H L776 + (-1 : ℝ) * (CF Γ p).H L386 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L861 [F38]
  rw [show [F30] ++ L861 ++ [F38] = L860 from rfl, show [F30] ++ L861 = L858 from rfl,
    show L861 ++ [F38] = L859 from rfl] at hh
  rw [i508 h, i506 h, i507 h, i509 h] at hh
  linarith

theorem row206 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L289 + (1 : ℝ) * (CF Γ p).H L671 + (-1 : ℝ) * (CF Γ p).H L776 + (-1 : ℝ) * (CF Γ p).H L240 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L241 [F38]
  rw [show [F10] ++ L241 ++ [F38] = L864 from rfl, show [F10] ++ L241 = L862 from rfl,
    show L241 ++ [F38] = L863 from rfl] at hh
  rw [i512 h, i510 h, i511 h, i116 h] at hh
  linarith

theorem row207 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L284 + (1 : ℝ) * (CF Γ p).H L618 + (-1 : ℝ) * (CF Γ p).H L344 + (-1 : ℝ) * (CF Γ p).H L472 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L868 [F43]
  rw [show [F10] ++ L868 ++ [F43] = L867 from rfl, show [F10] ++ L868 = L865 from rfl,
    show L868 ++ [F43] = L866 from rfl] at hh
  rw [i515 h, i513 h, i514 h, i516 h] at hh
  linarith

theorem row208 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L344 + (1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L246 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L875 [F6]
  rw [show [F10] ++ L875 ++ [F6] = L873 from rfl, show [F10] ++ L875 = L869 from rfl,
    show L875 ++ [F6] = L871 from rfl] at hh
  rw [i519 h, i517 h, i518 h, i520 h] at hh
  linarith

theorem row209 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L344 + (1 : ℝ) * (CF Γ p).H L844 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L835 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L883 [F6]
  rw [show [F10] ++ L883 ++ [F6] = L881 from rfl, show [F10] ++ L883 = L877 from rfl,
    show L883 ++ [F6] = L879 from rfl] at hh
  rw [i523 h, i521 h, i522 h, i524 h] at hh
  linarith

theorem row210 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L344 + (1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L888 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L889 [F6]
  rw [show [F10] ++ L889 ++ [F6] = L887 from rfl, show [F10] ++ L889 = L885 from rfl,
    show L889 ++ [F6] = L886 from rfl] at hh
  rw [i527 h, i525 h, i526 h, i528 h] at hh
  linarith

theorem row211 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L394 + (1 : ℝ) * (CF Γ p).H L503 + (-1 : ℝ) * (CF Γ p).H L768 + (-1 : ℝ) * (CF Γ p).H L819 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L820 [F41]
  rw [show [F10] ++ L820 ++ [F41] = L892 from rfl, show [F10] ++ L820 = L890 from rfl,
    show L820 ++ [F41] = L891 from rfl] at hh
  rw [i531 h, i529 h, i530 h, i481 h] at hh
  linarith

theorem row212 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L335 + (1 : ℝ) * (CF Γ p).H L445 + (-1 : ℝ) * (CF Γ p).H L311 + (-1 : ℝ) * (CF Γ p).H L802 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L896 [F6]
  rw [show [F10] ++ L896 ++ [F6] = L895 from rfl, show [F10] ++ L896 = L893 from rfl,
    show L896 ++ [F6] = L894 from rfl] at hh
  rw [i534 h, i532 h, i533 h, i535 h] at hh
  linarith

theorem row213 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L335 + (1 : ℝ) * (CF Γ p).H L722 + (-1 : ℝ) * (CF Γ p).H L551 + (-1 : ℝ) * (CF Γ p).H L592 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L593 [F37]
  rw [show [F10] ++ L593 ++ [F37] = L899 from rfl, show [F10] ++ L593 = L897 from rfl,
    show L593 ++ [F37] = L898 from rfl] at hh
  rw [i538 h, i536 h, i537 h, i323 h] at hh
  linarith

theorem row214 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L379 + (1 : ℝ) * (CF Γ p).H L794 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L904 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L905 [F37]
  rw [show [F10] ++ L905 ++ [F37] = L902 from rfl, show [F10] ++ L905 = L900 from rfl,
    show L905 ++ [F37] = L901 from rfl] at hh
  rw [i541 h, i539 h, i540 h, i542 h] at hh
  linarith

theorem row215 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L376 + (1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L909 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L910 [F6]
  rw [show [F10] ++ L910 ++ [F6] = L908 from rfl, show [F10] ++ L910 = L906 from rfl,
    show L910 ++ [F6] = L907 from rfl] at hh
  rw [i545 h, i543 h, i544 h, i546 h] at hh
  linarith

theorem row216 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L768 + (1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L917 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L918 [F7]
  rw [show [F10] ++ L918 ++ [F7] = L915 from rfl, show [F10] ++ L918 = L911 from rfl,
    show L918 ++ [F7] = L913 from rfl] at hh
  rw [i549 h, i547 h, i548 h, i550 h] at hh
  linarith

theorem row217 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L768 + (1 : ℝ) * (CF Γ p).H L921 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L924 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L925 [F43]
  rw [show [F10] ++ L925 ++ [F43] = L923 from rfl, show [F10] ++ L925 = L920 from rfl,
    show L925 ++ [F43] = L922 from rfl] at hh
  rw [i553 h, i551 h, i552 h, i554 h] at hh
  linarith

theorem row218 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L768 + (1 : ℝ) * (CF Γ p).H L927 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L930 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L931 [F43]
  rw [show [F10] ++ L931 ++ [F43] = L929 from rfl, show [F10] ++ L931 = L926 from rfl,
    show L931 ++ [F43] = L928 from rfl] at hh
  rw [i557 h, i555 h, i556 h, i558 h] at hh
  linarith

theorem row219 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L340 + (1 : ℝ) * (CF Γ p).H L933 + (-1 : ℝ) * (CF Γ p).H L935 + (-1 : ℝ) * (CF Γ p).H L937 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L938 [F106]
  rw [show [F10] ++ L938 ++ [F106] = L936 from rfl, show [F10] ++ L938 = L932 from rfl,
    show L938 ++ [F106] = L934 from rfl] at hh
  rw [i561 h, i559 h, i560 h, i562 h] at hh
  linarith

theorem row220 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L325 + (1 : ℝ) * (CF Γ p).H L714 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L943 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L944 [F34]
  rw [show [F10] ++ L944 ++ [F34] = L941 from rfl, show [F10] ++ L944 = L939 from rfl,
    show L944 ++ [F34] = L940 from rfl] at hh
  rw [i565 h, i563 h, i564 h, i566 h] at hh
  linarith

theorem row221 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L359 + (1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L706 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L951 [F7]
  rw [show [F10] ++ L951 ++ [F7] = L949 from rfl, show [F10] ++ L951 = L945 from rfl,
    show L951 ++ [F7] = L947 from rfl] at hh
  rw [i569 h, i567 h, i568 h, i570 h] at hh
  linarith

theorem row222 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L359 + (1 : ℝ) * (CF Γ p).H L636 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L833 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L959 [F43]
  rw [show [F10] ++ L959 ++ [F43] = L957 from rfl, show [F10] ++ L959 = L953 from rfl,
    show L959 ++ [F43] = L955 from rfl] at hh
  rw [i573 h, i571 h, i572 h, i574 h] at hh
  linarith

theorem row223 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L359 + (1 : ℝ) * (CF Γ p).H L2 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L761 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L964 [F7]
  rw [show [F10] ++ L964 ++ [F7] = L963 from rfl, show [F10] ++ L964 = L961 from rfl,
    show L964 ++ [F7] = L962 from rfl] at hh
  rw [i577 h, i575 h, i576 h, i578 h] at hh
  linarith

theorem row224 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L329 + (1 : ℝ) * (CF Γ p).H L722 + (-1 : ℝ) * (CF Γ p).H L551 + (-1 : ℝ) * (CF Γ p).H L800 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L968 [F34]
  rw [show [F10] ++ L968 ++ [F34] = L967 from rfl, show [F10] ++ L968 = L965 from rfl,
    show L968 ++ [F34] = L966 from rfl] at hh
  rw [i581 h, i579 h, i580 h, i582 h] at hh
  linarith

theorem row225 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L329 + (1 : ℝ) * (CF Γ p).H L687 + (-1 : ℝ) * (CF Γ p).H L551 + (-1 : ℝ) * (CF Γ p).H L685 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L686 [F34]
  rw [show [F10] ++ L686 ++ [F34] = L971 from rfl, show [F10] ++ L686 = L969 from rfl,
    show L686 ++ [F34] = L970 from rfl] at hh
  rw [i585 h, i583 h, i584 h, i385 h] at hh
  linarith

theorem row226 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L653 + (1 : ℝ) * (CF Γ p).H L844 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L975 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L976 [F6]
  rw [show [F10] ++ L976 ++ [F6] = L974 from rfl, show [F10] ++ L976 = L972 from rfl,
    show L976 ++ [F6] = L973 from rfl] at hh
  rw [i588 h, i586 h, i587 h, i589 h] at hh
  linarith

theorem row227 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L653 + (1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L580 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L980 [F41]
  rw [show [F10] ++ L980 ++ [F41] = L979 from rfl, show [F10] ++ L980 = L977 from rfl,
    show L980 ++ [F41] = L978 from rfl] at hh
  rw [i592 h, i590 h, i591 h, i593 h] at hh
  linarith

theorem row228 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L653 + (1 : ℝ) * (CF Γ p).H L599 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L641 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L984 [F6]
  rw [show [F10] ++ L984 ++ [F6] = L983 from rfl, show [F10] ++ L984 = L981 from rfl,
    show L984 ++ [F6] = L982 from rfl] at hh
  rw [i596 h, i594 h, i595 h, i597 h] at hh
  linarith

theorem row229 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L653 + (1 : ℝ) * (CF Γ p).H L986 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L989 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L990 [F6]
  rw [show [F10] ++ L990 ++ [F6] = L988 from rfl, show [F10] ++ L990 = L985 from rfl,
    show L990 ++ [F6] = L987 from rfl] at hh
  rw [i600 h, i598 h, i599 h, i601 h] at hh
  linarith

theorem row230 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L991 + (1 : ℝ) * (CF Γ p).H L466 + (-1 : ℝ) * (CF Γ p).H L994 + (-1 : ℝ) * (CF Γ p).H L792 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L996 [F6]
  rw [show [F10] ++ L996 ++ [F6] = L995 from rfl, show [F10] ++ L996 = L992 from rfl,
    show L996 ++ [F6] = L993 from rfl] at hh
  rw [i604 h, i602 h, i603 h, i605 h] at hh
  linarith

theorem row231 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L997 + (1 : ℝ) * (CF Γ p).H L453 + (-1 : ℝ) * (CF Γ p).H L1000 + (-1 : ℝ) * (CF Γ p).H L1002 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L1003 [F37]
  rw [show [F43] ++ L1003 ++ [F37] = L1001 from rfl, show [F43] ++ L1003 = L998 from rfl,
    show L1003 ++ [F37] = L999 from rfl] at hh
  rw [i608 h, i606 h, i607 h, i609 h] at hh
  linarith

theorem row232 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L413 + (1 : ℝ) * (CF Γ p).H L649 + (-1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L436 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1007 [F37]
  rw [show [F6] ++ L1007 ++ [F37] = L1006 from rfl, show [F6] ++ L1007 = L1004 from rfl,
    show L1007 ++ [F37] = L1005 from rfl] at hh
  rw [i612 h, i610 h, i611 h, i613 h] at hh
  linarith

theorem row233 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L466 + (1 : ℝ) * (CF Γ p).H L618 + (-1 : ℝ) * (CF Γ p).H L1000 + (-1 : ℝ) * (CF Γ p).H L643 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L644 [F37]
  rw [show [F6] ++ L644 ++ [F37] = L1010 from rfl, show [F6] ++ L644 = L1008 from rfl,
    show L644 ++ [F37] = L1009 from rfl] at hh
  rw [i616 h, i614 h, i615 h, i351 h] at hh
  linarith

theorem row234 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L994 + (1 : ℝ) * (CF Γ p).H L850 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L991 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1014 [F30]
  rw [show [F6] ++ L1014 ++ [F30] = L1013 from rfl, show [F6] ++ L1014 = L1011 from rfl,
    show L1014 ++ [F30] = L1012 from rfl] at hh
  rw [i619 h, i617 h, i618 h, i620 h] at hh
  linarith

theorem row235 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L432 + (1 : ℝ) * (CF Γ p).H L558 + (-1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L1018 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1019 [F7]
  rw [show [F6] ++ L1019 ++ [F7] = L1017 from rfl, show [F6] ++ L1019 = L1015 from rfl,
    show L1019 ++ [F7] = L1016 from rfl] at hh
  rw [i623 h, i621 h, i622 h, i624 h] at hh
  linarith

theorem row236 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L469 + (1 : ℝ) * (CF Γ p).H L573 + (-1 : ℝ) * (CF Γ p).H L1022 + (-1 : ℝ) * (CF Γ p).H L669 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1024 [F7]
  rw [show [F6] ++ L1024 ++ [F7] = L1023 from rfl, show [F6] ++ L1024 = L1020 from rfl,
    show L1024 ++ [F7] = L1021 from rfl] at hh
  rw [i627 h, i625 h, i626 h, i628 h] at hh
  linarith

theorem row237 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L441 + (1 : ℝ) * (CF Γ p).H L789 + (-1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L787 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1028 [F37]
  rw [show [F6] ++ L1028 ++ [F37] = L1027 from rfl, show [F6] ++ L1028 = L1025 from rfl,
    show L1028 ++ [F37] = L1026 from rfl] at hh
  rw [i631 h, i629 h, i630 h, i632 h] at hh
  linarith

theorem row238 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L491 + (1 : ℝ) * (CF Γ p).H L1030 + (-1 : ℝ) * (CF Γ p).H L750 + (-1 : ℝ) * (CF Γ p).H L511 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L591 [F38]
  rw [show [F41] ++ L591 ++ [F38] = L1032 from rfl, show [F41] ++ L591 = L1029 from rfl,
    show L591 ++ [F38] = L1031 from rfl] at hh
  rw [i635 h, i633 h, i634 h, i322 h] at hh
  linarith

theorem row239 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L924 + (1 : ℝ) * (CF Γ p).H L570 + (-1 : ℝ) * (CF Γ p).H L744 + (-1 : ℝ) * (CF Γ p).H L383 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L1036 [F7]
  rw [show [F41] ++ L1036 ++ [F7] = L1035 from rfl, show [F41] ++ L1036 = L1033 from rfl,
    show L1036 ++ [F7] = L1034 from rfl] at hh
  rw [i638 h, i636 h, i637 h, i639 h] at hh
  linarith

theorem row240 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L486 + (1 : ℝ) * (CF Γ p).H L1038 + (-1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L493 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L1041 [F30]
  rw [show [F7] ++ L1041 ++ [F30] = L1040 from rfl, show [F7] ++ L1041 = L1037 from rfl,
    show L1041 ++ [F30] = L1039 from rfl] at hh
  rw [i642 h, i640 h, i641 h, i643 h] at hh
  linarith

theorem row241 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L573 + (1 : ℝ) * (CF Γ p).H L930 + (-1 : ℝ) * (CF Γ p).H L755 + (-1 : ℝ) * (CF Γ p).H L299 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L300 [F8]
  rw [show [F7] ++ L300 ++ [F8] = L1044 from rfl, show [F7] ++ L300 = L1042 from rfl,
    show L300 ++ [F8] = L1043 from rfl] at hh
  rw [i646 h, i644 h, i645 h, i144 h] at hh
  linarith

theorem row242 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L975 + (1 : ℝ) * (CF Γ p).H L1046 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L327 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L328 [F34]
  rw [show [F7] ++ L328 ++ [F34] = L1048 from rfl, show [F7] ++ L328 = L1045 from rfl,
    show L328 ++ [F34] = L1047 from rfl] at hh
  rw [i649 h, i647 h, i648 h, i161 h] at hh
  linarith

theorem row243 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L589 + (1 : ℝ) * (CF Γ p).H L1051 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L712 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L713 [F15]
  rw [show [F43] ++ L713 ++ [F15] = L1053 from rfl, show [F43] ++ L713 = L1050 from rfl,
    show L713 ++ [F15] = L1052 from rfl] at hh
  rw [i652 h, i650 h, i651 h, i405 h] at hh
  linarith

theorem row244 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L888 + (1 : ℝ) * (CF Γ p).H L679 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L282 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L283 [F15]
  rw [show [F43] ++ L283 ++ [F15] = L1055 from rfl, show [F43] ++ L283 = L889 from rfl,
    show L283 ++ [F15] = L779 from rfl] at hh
  rw [i653 h, i528 h, i452 h, i133 h] at hh
  linarith

theorem row245 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L888 + (1 : ℝ) * (CF Γ p).H L1058 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L342 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L343 [F15]
  rw [show [F43] ++ L343 ++ [F15] = L1060 from rfl, show [F43] ++ L343 = L1057 from rfl,
    show L343 ++ [F15] = L1059 from rfl] at hh
  rw [i656 h, i654 h, i655 h, i169 h] at hh
  linarith

theorem row246 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L641 + (1 : ℝ) * (CF Γ p).H L1063 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L824 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L1067 [F73]
  rw [show [F43] ++ L1067 ++ [F73] = L1065 from rfl, show [F43] ++ L1067 = L1062 from rfl,
    show L1067 ++ [F73] = L1064 from rfl] at hh
  rw [i659 h, i657 h, i658 h, i660 h] at hh
  linarith

theorem row247 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L551 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L1046 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1071 [F10]
  rw [show [F6] ++ L1071 ++ [F10] = L1070 from rfl, show [F6] ++ L1071 = L1068 from rfl,
    show L1071 ++ [F10] = L1069 from rfl] at hh
  rw [i663 h, i661 h, i662 h, i664 h] at hh
  linarith

theorem row248 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L935 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L933 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L934 [F10]
  rw [show [F6] ++ L934 ++ [F10] = L1074 from rfl, show [F6] ++ L934 = L1072 from rfl,
    show L934 ++ [F10] = L1073 from rfl] at hh
  rw [i667 h, i665 h, i666 h, i560 h] at hh
  linarith

theorem row249 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L625 + (1 : ℝ) * (CF Γ p).H L1075 + (-1 : ℝ) * (CF Γ p).H L927 + (-1 : ℝ) * (CF Γ p).H L623 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L624 [F37]
  rw [show [F43] ++ L624 ++ [F37] = L1077 from rfl, show [F43] ++ L624 = L626 from rfl,
    show L624 ++ [F37] = L1076 from rfl] at hh
  rw [i669 h, i342 h, i668 h, i341 h] at hh
  linarith

theorem row250 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L629 + (1 : ℝ) * (CF Γ p).H L729 + (-1 : ℝ) * (CF Γ p).H L921 + (-1 : ℝ) * (CF Γ p).H L627 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L628 [F34]
  rw [show [F43] ++ L628 ++ [F34] = L1079 from rfl, show [F43] ++ L628 = L630 from rfl,
    show L628 ++ [F34] = L1078 from rfl] at hh
  rw [i671 h, i344 h, i670 h, i343 h] at hh
  linarith

theorem row251 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L909 + (1 : ℝ) * (CF Γ p).H L679 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L829 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L1084 [F30]
  rw [show [F43] ++ L1084 ++ [F30] = L1082 from rfl, show [F43] ++ L1084 = L1080 from rfl,
    show L1084 ++ [F30] = L1081 from rfl] at hh
  rw [i674 h, i672 h, i673 h, i675 h] at hh
  linarith

theorem row252 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L657 + (1 : ℝ) * (CF Γ p).H L1000 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L1088 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L1089 [F6]
  rw [show [F10] ++ L1089 ++ [F6] = L1087 from rfl, show [F10] ++ L1089 = L1085 from rfl,
    show L1089 ++ [F6] = L1086 from rfl] at hh
  rw [i678 h, i676 h, i677 h, i679 h] at hh
  linarith

theorem row253 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L855 + (1 : ℝ) * (CF Γ p).H L5 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L853 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L1093 [F16]
  rw [show [F10] ++ L1093 ++ [F16] = L1092 from rfl, show [F10] ++ L1093 = L1090 from rfl,
    show L1093 ++ [F16] = L1091 from rfl] at hh
  rw [i682 h, i680 h, i681 h, i683 h] at hh
  linarith

theorem row254 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L1022 + (1 : ℝ) * (CF Γ p).H L8 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L1051 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L1096 [F25]
  rw [show [F6] ++ L1096 ++ [F25] = L1095 from rfl, show [F6] ++ L1096 = L1094 from rfl,
    show L1096 ++ [F25] = L9 from rfl] at hh
  rw [i685 h, i684 h, i5 h, i686 h] at hh
  linarith

theorem row255 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L1097 + (1 : ℝ) * (CF Γ p).H L314 + (-1 : ℝ) * (CF Γ p).H L183 + (-1 : ℝ) * (CF Γ p).H L16 = 0 := by
  have hh : (C1 Γ p).H (L1101 ++ L1102 ++ L17) + (C1 Γ p).H L17 = (C1 Γ p).H (L1101 ++ L17) + (C1 Γ p).H (L1102 ++ L17) :=
    Conf.H_copy_ci (src := src0) (V := V0) (hv0 h) (by decide) L1101 L1102 L1101 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1101 ++ L1102 ++ L17 = L1100 from rfl, show L1101 ++ L17 = L1099 from rfl, show L1102 ++ L17 = L1098 from rfl] at hh
  rw [← lift1 h L1100 (by decide) (by decide), ← lift1 h L17 (by decide) (by decide), ← lift1 h L1099 (by decide) (by decide), ← lift1 h L1098 (by decide) (by decide)] at hh
  rw [i689 h, i9 h, i688 h, i687 h] at hh
  linarith

theorem row256 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L154 + (1 : ℝ) * (CF Γ p).H L183 + (-1 : ℝ) * (CF Γ p).H L305 + (-1 : ℝ) * (CF Γ p).H L107 = 0 := by
  have hh : (C2 Γ p).H (L1106 ++ L1107 ++ L108) + (C2 Γ p).H L108 = (C2 Γ p).H (L1106 ++ L108) + (C2 Γ p).H (L1107 ++ L108) :=
    Conf.H_copy_ci (src := src1) (V := V1) (hv1 h) (by decide) L1106 L1107 L1106 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1106 ++ L1107 ++ L108 = L1105 from rfl, show L1106 ++ L108 = L1104 from rfl, show L1107 ++ L108 = L1103 from rfl] at hh
  rw [← lift2 h L1105 (by decide), ← lift2 h L108 (by decide), ← lift2 h L1104 (by decide), ← lift2 h L1103 (by decide)] at hh
  rw [i692 h, i53 h, i691 h, i690 h] at hh
  linarith

theorem row257 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L215 + (1 : ℝ) * (CF Γ p).H L305 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L111 = 0 := by
  have hh : (CF Γ p).H (L1111 ++ L1112 ++ L112) + (CF Γ p).H L112 = (CF Γ p).H (L1111 ++ L112) + (CF Γ p).H (L1112 ++ L112) :=
    Conf.H_copy_ci (src := src2) (V := V2) (hv2 h) (by decide) L1111 L1112 L1106 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1111 ++ L1112 ++ L112 = L1110 from rfl, show L1111 ++ L112 = L1109 from rfl, show L1112 ++ L112 = L1108 from rfl] at hh
  rw [i695 h, i55 h, i694 h, i693 h] at hh
  linarith

theorem row258 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L338 + (5 : ℝ) * (CF Γ p).H L618 + (-12 : ℝ) * (CF Γ p).H L344 + (6 : ℝ) * (CF Γ p).H L198 + (2 : ℝ) * (CF Γ p).H L340 + (-4 : ℝ) * (CF Γ p).H L250 + (7 : ℝ) * (CF Γ p).H L741 + (2 : ℝ) * (CF Γ p).H L252 + (-3 : ℝ) * (CF Γ p).H L14 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L676 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1113 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1114 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1115 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1116 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1117 from rfl, show ([1] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L251 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1118 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1119 from rfl, show ([2] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L15 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L676, L251, L15, L102, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1120 from rfl] at hL
  rw [i377 h, i696 h, i697 h, i698 h, i699 h, i700 h, i121 h, i701 h, i702 h, i8 h, i703 h] at hL
  linarith

theorem row259 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L79 + (7 : ℝ) * (CF Γ p).H L829 + (-12 : ℝ) * (CF Γ p).H L235 + (5 : ℝ) * (CF Γ p).H L417 + (2 : ℝ) * (CF Γ p).H L709 + (-5 : ℝ) * (CF Γ p).H L209 + (6 : ℝ) * (CF Γ p).H L592 + (2 : ℝ) * (CF Γ p).H L397 + (-1 : ℝ) * (CF Γ p).H L26 := by
  have hL := lem_dfz5 ((CF Γ p).lsp ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L80 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1122 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1123 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1124 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1125 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1126 from rfl, show ([1] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L210 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1127 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1128 from rfl, show ([2] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L27 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L80, L210, L27, L234, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L236 from rfl] at hL
  rw [i39 h, i704 h, i705 h, i706 h, i707 h, i708 h, i102 h, i709 h, i710 h, i14 h, i114 h] at hL
  linarith

theorem row260 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L121 + (9 : ℝ) * (CF Γ p).H L1018 + (-14 : ℝ) * (CF Γ p).H L432 + (-3 : ℝ) * (CF Γ p).H L359 + (9 : ℝ) * (CF Γ p).H L425 + (3 : ℝ) * (CF Γ p).H L937 + (-8 : ℝ) * (CF Γ p).H L91 + (13 : ℝ) * (CF Γ p).H L115 + (3 : ℝ) * (CF Γ p).H L943 + (-5 : ℝ) * (CF Γ p).H L18 + (-3 : ℝ) * (CF Γ p).H L139 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L122 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1129 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1130 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1131 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1133 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L938 from rfl, show ([1] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L92 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1134 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1135 from rfl, show ([2] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L19 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L122, L92, L19, L138, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L140 from rfl] at hL
  rw [i60 h, i711 h, i712 h, i713 h, i714 h, i562 h, i45 h, i715 h, i716 h, i10 h, i69 h] at hL
  linarith

theorem row261 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L439 + (5 : ℝ) * (CF Γ p).H L924 + (-12 : ℝ) * (CF Γ p).H L768 + (6 : ℝ) * (CF Γ p).H L394 + (2 : ℝ) * (CF Γ p).H L441 + (-4 : ℝ) * (CF Γ p).H L383 + (7 : ℝ) * (CF Γ p).H L224 + (2 : ℝ) * (CF Γ p).H L301 + (-3 : ℝ) * (CF Γ p).H L85 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1136 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1137 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1138 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1139 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1140 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1141 from rfl, show ([1] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1036 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1142 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1143 from rfl, show ([2] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L86 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1136, L1036, L86, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1144 from rfl] at hL
  rw [i717 h, i718 h, i719 h, i720 h, i721 h, i722 h, i639 h, i723 h, i724 h, i42 h, i725 h] at hL
  linarith

theorem row262 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-9 : ℝ) * (CF Γ p).H L383 + (9 : ℝ) * (CF Γ p).H L224 + (-11 : ℝ) * (CF Γ p).H L768 + (-3 : ℝ) * (CF Γ p).H L537 + (11 : ℝ) * (CF Γ p).H L924 + (-4 : ℝ) * (CF Γ p).H L744 + (7 : ℝ) * (CF Γ p).H L570 + (-7 : ℝ) * (CF Γ p).H L85 + (9 : ℝ) * (CF Γ p).H L394 + (3 : ℝ) * (CF Γ p).H L773 + (-2 : ℝ) * (CF Γ p).H L439 + (-3 : ℝ) * (CF Γ p).H L848 := by
  have hL := lem_dfz33 ((CF Γ p).lsp ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1036 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1142 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1146 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1147 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1148 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1149 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1150 from rfl, show ([1] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L86 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1151 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1152 from rfl, show ([2] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1136 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1036, L86, L1136, L197, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1153 from rfl] at hL
  rw [i639 h, i723 h, i726 h, i727 h, i728 h, i729 h, i730 h, i42 h, i731 h, i732 h, i717 h, i733 h] at hL
  linarith

theorem row263 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L287 + (6 : ℝ) * (CF Γ p).H L649 + (-8 : ℝ) * (CF Γ p).H L530 + (-2 : ℝ) * (CF Γ p).H L653 + (5 : ℝ) * (CF Γ p).H L445 + (2 : ℝ) * (CF Γ p).H L580 + (-5 : ℝ) * (CF Γ p).H L211 + (7 : ℝ) * (CF Γ p).H L909 + (2 : ℝ) * (CF Γ p).H L641 + (-2 : ℝ) * (CF Γ p).H L802 + (-2 : ℝ) * (CF Γ p).H L1058 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1154 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1155 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1156 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1157 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1158 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1159 from rfl, show ([1] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L212 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1160 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1161 from rfl, show ([2] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L896 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1154, L212, L896, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1162 from rfl] at hL
  rw [i734 h, i735 h, i736 h, i737 h, i738 h, i739 h, i103 h, i740 h, i741 h, i535 h, i742 h] at hL
  linarith

theorem row264 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L333 + (7 : ℝ) * (CF Γ p).H L507 + (-19 : ℝ) * (CF Γ p).H L311 + (11 : ℝ) * (CF Γ p).H L149 + (3 : ℝ) * (CF Γ p).H L335 + (-5 : ℝ) * (CF Γ p).H L505 + (11 : ℝ) * (CF Γ p).H L741 + (3 : ℝ) * (CF Γ p).H L445 + (-6 : ℝ) * (CF Γ p).H L244 := by
  have hL := lem_dfz56 ((CF Γ p).lsp ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1163 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1164 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1165 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1166 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1167 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1168 from rfl, show ([1] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L506 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1169 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1170 from rfl, show ([2] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L245 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1163, L506, L245, L53, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1171 from rfl] at hL
  rw [i743 h, i744 h, i745 h, i746 h, i747 h, i748 h, i269 h, i749 h, i750 h, i118 h, i751 h] at hL
  linarith

theorem row265 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L314 + (9 : ℝ) * (CF Γ p).H L367 + (-20 : ℝ) * (CF Γ p).H L352 + (9 : ℝ) * (CF Γ p).H L254 + (3 : ℝ) * (CF Γ p).H L183 + (-8 : ℝ) * (CF Γ p).H L381 + (13 : ℝ) * (CF Γ p).H L408 + (3 : ℝ) * (CF Γ p).H L554 + (-5 : ℝ) * (CF Γ p).H L20 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L315 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1173 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1174 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1175 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1176 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1177 from rfl, show ([1] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L382 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1179 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1180 from rfl, show ([2] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L21 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L315, L382, L21, L126, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1181 from rfl] at hL
  rw [i152 h, i752 h, i753 h, i754 h, i755 h, i756 h, i192 h, i757 h, i758 h, i11 h, i759 h] at hL
  linarith

theorem row266 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L436 + (9 : ℝ) * (CF Γ p).H L621 + (-20 : ℝ) * (CF Γ p).H L352 + (9 : ℝ) * (CF Γ p).H L413 + (3 : ℝ) * (CF Γ p).H L408 + (-8 : ℝ) * (CF Γ p).H L46 + (13 : ℝ) * (CF Γ p).H L68 + (3 : ℝ) * (CF Γ p).H L997 + (-5 : ℝ) * (CF Γ p).H L427 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1007 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1184 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1185 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1186 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1187 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1188 from rfl, show ([1] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L47 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1189 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1190 from rfl, show ([2] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1183 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1007, L47, L1183, L189, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1191 from rfl] at hL
  rw [i613 h, i760 h, i761 h, i762 h, i763 h, i764 h, i24 h, i765 h, i766 h, i767 h, i768 h] at hL
  linarith

theorem row267 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L575 + (14 : ℝ) * (CF Γ p).H L449 + (-28 : ℝ) * (CF Γ p).H L545 + (15 : ℝ) * (CF Γ p).H L246 + (4 : ℝ) * (CF Γ p).H L486 + (-13 : ℝ) * (CF Γ p).H L1199 + (23 : ℝ) * (CF Γ p).H L729 + (4 : ℝ) * (CF Γ p).H L1038 + (-10 : ℝ) * (CF Γ p).H L205 + (-4 : ℝ) * (CF Γ p).H L1075 := by
  have hL := lem_dfz77 ((CF Γ p).lsp ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L576 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1194 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1195 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1196 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1197 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1198 from rfl, show ([1] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1193 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1200 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1201 from rfl, show ([2] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L796 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L576, L1193, L796, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1202 from rfl] at hL
  rw [i311 h, i769 h, i770 h, i771 h, i772 h, i773 h, i774 h, i775 h, i776 h, i464 h, i777 h] at hL
  linarith

theorem row268 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L434 + (9 : ℝ) * (CF Γ p).H L413 + (-20 : ℝ) * (CF Γ p).H L352 + (9 : ℝ) * (CF Γ p).H L257 + (3 : ℝ) * (CF Γ p).H L367 + (-8 : ℝ) * (CF Γ p).H L425 + (13 : ℝ) * (CF Γ p).H L254 + (3 : ℝ) * (CF Γ p).H L548 + (-5 : ℝ) * (CF Γ p).H L24 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1203 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1205 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1206 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1207 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1208 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1209 from rfl, show ([1] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1204 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1210 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1211 from rfl, show ([2] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L25 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1203, L1204, L25, L162, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1212 from rfl] at hL
  rw [i778 h, i779 h, i780 h, i781 h, i782 h, i783 h, i784 h, i785 h, i786 h, i13 h, i787 h] at hL
  linarith

theorem row269 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L511 + (9 : ℝ) * (CF Γ p).H L491 + (-20 : ℝ) * (CF Γ p).H L305 + (9 : ℝ) * (CF Γ p).H L271 + (3 : ℝ) * (CF Γ p).H L297 + (-8 : ℝ) * (CF Γ p).H L499 + (13 : ℝ) * (CF Γ p).H L63 + (3 : ℝ) * (CF Γ p).H L533 + (-5 : ℝ) * (CF Γ p).H L44 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L591 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1215 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1216 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1217 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1218 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1219 from rfl, show ([1] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1214 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1220 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1221 from rfl, show ([2] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L45 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L591, L1214, L45, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1222 from rfl] at hL
  rw [i322 h, i788 h, i789 h, i790 h, i791 h, i792 h, i793 h, i794 h, i795 h, i23 h, i796 h] at hL
  linarith

theorem row270 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L509 + (9 : ℝ) * (CF Γ p).H L491 + (-20 : ℝ) * (CF Γ p).H L305 + (9 : ℝ) * (CF Γ p).H L268 + (3 : ℝ) * (CF Γ p).H L319 + (-8 : ℝ) * (CF Γ p).H L497 + (13 : ℝ) * (CF Γ p).H L54 + (3 : ℝ) * (CF Γ p).H L527 + (-5 : ℝ) * (CF Γ p).H L40 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1224 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1226 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1227 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1228 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1229 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1230 from rfl, show ([1] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1225 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1231 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1232 from rfl, show ([2] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L41 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1224, L1225, L41, L80, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1233 from rfl] at hL
  rw [i797 h, i798 h, i799 h, i800 h, i801 h, i802 h, i803 h, i804 h, i805 h, i21 h, i806 h] at hL
  linarith

theorem row271 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L248 + (9 : ℝ) * (CF Γ p).H L215 + (-20 : ℝ) * (CF Γ p).H L352 + (9 : ℝ) * (CF Γ p).H L68 + (3 : ℝ) * (CF Γ p).H L257 + (-8 : ℝ) * (CF Γ p).H L411 + (13 : ℝ) * (CF Γ p).H L413 + (3 : ℝ) * (CF Γ p).H L371 + (-5 : ℝ) * (CF Γ p).H L427 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1235 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1239 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1240 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1241 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1242 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1243 from rfl, show ([1] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1236 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1244 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1245 from rfl, show ([2] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1183 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1235, L1236, L1183, L1237, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1246 from rfl] at hL
  rw [i807 h, i808 h, i809 h, i810 h, i811 h, i812 h, i813 h, i814 h, i815 h, i767 h, i816 h] at hL
  linarith

theorem row272 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L602 + (6 : ℝ) * (CF Γ p).H L224 + (-12 : ℝ) * (CF Γ p).H L537 + (5 : ℝ) * (CF Γ p).H L154 + (2 : ℝ) * (CF Γ p).H L260 + (-5 : ℝ) * (CF Γ p).H L383 + (7 : ℝ) * (CF Γ p).H L722 + (2 : ℝ) * (CF Γ p).H L570 + (-2 : ℝ) * (CF Γ p).H L489 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L603 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1249 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1250 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1251 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1252 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1253 from rfl, show ([1] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1036 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1254 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1255 from rfl, show ([2] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1248 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L603, L1036, L1248, L191, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1256 from rfl] at hL
  rw [i328 h, i817 h, i818 h, i819 h, i820 h, i821 h, i639 h, i822 h, i823 h, i824 h, i825 h] at hL
  linarith

theorem row273 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L800 + (5 : ℝ) * (CF Γ p).H L649 + (-12 : ℝ) * (CF Γ p).H L653 + (6 : ℝ) * (CF Γ p).H L265 + (2 : ℝ) * (CF Γ p).H L329 + (-4 : ℝ) * (CF Γ p).H L287 + (7 : ℝ) * (CF Γ p).H L289 + (2 : ℝ) * (CF Γ p).H L580 + (-3 : ℝ) * (CF Γ p).H L817 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L968 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1258 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1259 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1260 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1261 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1262 from rfl, show ([1] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1154 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1263 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1264 from rfl, show ([2] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L818 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L968, L1154, L818, L686, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1265 from rfl] at hL
  rw [i582 h, i826 h, i827 h, i828 h, i829 h, i830 h, i734 h, i831 h, i832 h, i480 h, i833 h] at hL
  linarith

theorem row274 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-19 : ℝ) * (CF Γ p).H L669 + (18 : ℝ) * (CF Γ p).H L645 + (-27 : ℝ) * (CF Γ p).H L608 + (-6 : ℝ) * (CF Γ p).H L657 + (28 : ℝ) * (CF Γ p).H L469 + (-11 : ℝ) * (CF Γ p).H L1022 + (17 : ℝ) * (CF Γ p).H L573 + (-16 : ℝ) * (CF Γ p).H L643 + (25 : ℝ) * (CF Γ p).H L888 + (6 : ℝ) * (CF Γ p).H L1088 + (-9 : ℝ) * (CF Γ p).H L937 + (-6 : ℝ) * (CF Γ p).H L1063 := by
  have hL := lem_dfz35 ((CF Γ p).lsp ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1024 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1268 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1269 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1270 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1271 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1272 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1273 from rfl, show ([1] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L644 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1274 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1275 from rfl, show ([2] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L938 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1024, L644, L938, L1267, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1276 from rfl] at hL
  rw [i628 h, i834 h, i835 h, i836 h, i837 h, i838 h, i839 h, i351 h, i840 h, i841 h, i562 h, i842 h] at hL
  linarith

theorem row275 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L295 + (9 : ℝ) * (CF Γ p).H L1088 + (-14 : ℝ) * (CF Γ p).H L0 + (-3 : ℝ) * (CF Γ p).H L657 + (9 : ℝ) * (CF Γ p).H L909 + (3 : ℝ) * (CF Γ p).H L297 + (-8 : ℝ) * (CF Γ p).H L643 + (13 : ℝ) * (CF Γ p).H L888 + (3 : ℝ) * (CF Γ p).H L645 + (-5 : ℝ) * (CF Γ p).H L427 + (-3 : ℝ) * (CF Γ p).H L1030 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1277 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1278 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1279 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1281 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1282 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1283 from rfl, show ([1] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L644 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1284 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L646 from rfl, show ([2] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1183 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1277, L644, L1183, L27, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1285 from rfl] at hL
  rw [i843 h, i844 h, i845 h, i846 h, i847 h, i848 h, i351 h, i849 h, i352 h, i767 h, i850 h] at hL
  linarith

theorem row276 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L121 + (9 : ℝ) * (CF Γ p).H L802 + (-14 : ℝ) * (CF Γ p).H L335 + (-3 : ℝ) * (CF Γ p).H L311 + (9 : ℝ) * (CF Γ p).H L331 + (3 : ℝ) * (CF Γ p).H L244 + (-8 : ℝ) * (CF Γ p).H L52 + (13 : ℝ) * (CF Γ p).H L28 + (3 : ℝ) * (CF Γ p).H L904 + (-5 : ℝ) * (CF Γ p).H L16 + (-3 : ℝ) * (CF Γ p).H L77 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L122 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L896 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1286 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1287 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1289 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1290 from rfl, show ([1] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L53 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1291 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1292 from rfl, show ([2] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L17 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L122, L53, L17, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L78 from rfl] at hL
  rw [i60 h, i535 h, i851 h, i852 h, i853 h, i854 h, i27 h, i855 h, i856 h, i9 h, i38 h] at hL
  linarith

theorem row277 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L287 + (9 : ℝ) * (CF Γ p).H L445 + (-14 : ℝ) * (CF Γ p).H L311 + (-3 : ℝ) * (CF Γ p).H L986 + (9 : ℝ) * (CF Γ p).H L277 + (3 : ℝ) * (CF Γ p).H L989 + (-8 : ℝ) * (CF Γ p).H L119 + (13 : ℝ) * (CF Γ p).H L54 + (3 : ℝ) * (CF Γ p).H L474 + (-5 : ℝ) * (CF Γ p).H L497 + (-3 : ℝ) * (CF Γ p).H L766 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1154 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1293 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1294 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1295 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1296 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1297 from rfl, show ([1] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L120 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1298 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1299 from rfl, show ([2] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1225 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1154, L120, L1225, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1300 from rfl] at hL
  rw [i734 h, i857 h, i858 h, i859 h, i860 h, i861 h, i59 h, i862 h, i863 h, i803 h, i864 h] at hL
  linarith

theorem row278 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L57 + (11 : ℝ) * (CF Γ p).H L40 + (-13 : ℝ) * (CF Γ p).H L54 + (-3 : ℝ) * (CF Γ p).H L516 + (7 : ℝ) * (CF Γ p).H L119 + (3 : ℝ) * (CF Γ p).H L784 + (-9 : ℝ) * (CF Γ p).H L133 + (11 : ℝ) * (CF Γ p).H L28 + (3 : ℝ) * (CF Γ p).H L274 + (-2 : ℝ) * (CF Γ p).H L52 + (-3 : ℝ) * (CF Γ p).H L909 := by
  have hL := lem_dfz60 ((CF Γ p).lsp ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L58 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1301 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1302 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1303 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1304 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1305 from rfl, show ([1] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L134 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1306 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1307 from rfl, show ([2] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L53 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L58, L134, L53, L230, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1308 from rfl] at hL
  rw [i29 h, i865 h, i866 h, i867 h, i868 h, i869 h, i66 h, i870 h, i871 h, i27 h, i872 h] at hL
  linarith

theorem row279 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L509 + (9 : ℝ) * (CF Γ p).H L491 + (-20 : ℝ) * (CF Γ p).H L305 + (9 : ℝ) * (CF Γ p).H L319 + (3 : ℝ) * (CF Γ p).H L268 + (-8 : ℝ) * (CF Γ p).H L499 + (13 : ℝ) * (CF Γ p).H L63 + (3 : ℝ) * (CF Γ p).H L533 + (-5 : ℝ) * (CF Γ p).H L32 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1224 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1309 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1310 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1311 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1312 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1313 from rfl, show ([1] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1214 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1314 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1315 from rfl, show ([2] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L33 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1224, L1214, L33, L58, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1316 from rfl] at hL
  rw [i797 h, i873 h, i874 h, i875 h, i876 h, i877 h, i793 h, i878 h, i879 h, i17 h, i880 h] at hL
  linarith

theorem row280 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L436 + (6 : ℝ) * (CF Γ p).H L413 + (-12 : ℝ) * (CF Γ p).H L352 + (5 : ℝ) * (CF Γ p).H L408 + (2 : ℝ) * (CF Γ p).H L621 + (-5 : ℝ) * (CF Γ p).H L425 + (7 : ℝ) * (CF Γ p).H L254 + (2 : ℝ) * (CF Γ p).H L548 + (-2 : ℝ) * (CF Γ p).H L20 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1007 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1318 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1319 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1320 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1321 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1322 from rfl, show ([1] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1204 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1323 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1324 from rfl, show ([2] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L21 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1007, L1204, L21, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1325 from rfl] at hL
  rw [i613 h, i881 h, i882 h, i883 h, i884 h, i885 h, i784 h, i886 h, i887 h, i11 h, i888 h] at hL
  linarith

theorem row281 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L12 + (9 : ℝ) * (CF Γ p).H L50 + (-17 : ℝ) * (CF Γ p).H L997 + (9 : ℝ) * (CF Γ p).H L24 + (3 : ℝ) * (CF Γ p).H L46 + (-8 : ℝ) * (CF Γ p).H L213 + (13 : ℝ) * (CF Γ p).H L188 + (3 : ℝ) * (CF Γ p).H L1002 + (-5 : ℝ) * (CF Γ p).H L186 + (-3 : ℝ) * (CF Γ p).H L797 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L13 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L823 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1327 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1328 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1329 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1330 from rfl, show ([1] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L214 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1331 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1332 from rfl, show ([2] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L187 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L13, L214, L187, L72, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1333 from rfl] at hL
  rw [i7 h, i483 h, i889 h, i890 h, i891 h, i892 h, i104 h, i893 h, i894 h, i91 h, i895 h] at hL
  linarith

theorem row282 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L121 + (7 : ℝ) * (CF Γ p).H L802 + (-8 : ℝ) * (CF Γ p).H L311 + (-2 : ℝ) * (CF Γ p).H L335 + (5 : ℝ) * (CF Γ p).H L244 + (2 : ℝ) * (CF Γ p).H L331 + (-5 : ℝ) * (CF Γ p).H L209 + (6 : ℝ) * (CF Γ p).H L817 + (2 : ℝ) * (CF Γ p).H L592 + (-1 : ℝ) * (CF Γ p).H L10 + (-2 : ℝ) * (CF Γ p).H L14 := by
  have hL := lem_dfz5 ((CF Γ p).lsp ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L122 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1334 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1335 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1337 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1338 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1339 from rfl, show ([1] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L210 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1340 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1341 from rfl, show ([2] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L11 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L122, L210, L11, L13, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L15 from rfl] at hL
  rw [i60 h, i896 h, i897 h, i898 h, i899 h, i900 h, i102 h, i901 h, i902 h, i6 h, i8 h] at hL
  linarith

theorem row283 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-12 : ℝ) * (CF Γ p).H L692 + (14 : ℝ) * (CF Γ p).H L495 + (-38 : ℝ) * (CF Γ p).H L524 + (21 : ℝ) * (CF Γ p).H L252 + (11 : ℝ) * (CF Γ p).H L606 + (-13 : ℝ) * (CF Γ p).H L493 + (22 : ℝ) * (CF Γ p).H L486 + (4 : ℝ) * (CF Γ p).H L821 + (-9 : ℝ) * (CF Γ p).H L575 := by
  have hL := lem_dfz107 ((CF Γ p).lsp ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1342 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1343 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1344 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1345 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1346 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1347 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1348 from rfl, show ([1] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1041 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1349 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1350 from rfl, show ([2] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L576 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1342, L1041, L576, L264, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1351 from rfl] at hL
  rw [i903 h, i904 h, i905 h, i906 h, i907 h, i908 h, i909 h, i643 h, i910 h, i911 h, i311 h, i912 h] at hL
  linarith

theorem row284 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-12 : ℝ) * (CF Γ p).H L669 + (78 : ℝ) * (CF Γ p).H L645 + (-144 : ℝ) * (CF Γ p).H L608 + (-22 : ℝ) * (CF Γ p).H L0 + (78 : ℝ) * (CF Γ p).H L469 + (11 : ℝ) * (CF Γ p).H L516 + (-77 : ℝ) * (CF Γ p).H L383 + (143 : ℝ) * (CF Γ p).H L224 + (11 : ℝ) * (CF Γ p).H L551 + (-66 : ℝ) * (CF Γ p).H L463 := by
  have hL := lem_matus11 ((CF Γ p).lsp ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1024 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1354 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1355 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1356 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1357 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1358 from rfl, show ([1] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1036 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1359 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1360 from rfl, show ([2] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L471 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1024, L1036, L471, L1353, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1361 from rfl] at hL
  rw [i628 h, i913 h, i914 h, i915 h, i916 h, i917 h, i639 h, i918 h, i919 h, i247 h, i920 h] at hL
  linarith

theorem row285 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-8 : ℝ) * (CF Γ p).H L10 + (36 : ℝ) * (CF Γ p).H L809 + (-71 : ℝ) * (CF Γ p).H L242 + (36 : ℝ) * (CF Γ p).H L238 + (7 : ℝ) * (CF Γ p).H L240 + (-35 : ℝ) * (CF Γ p).H L97 + (63 : ℝ) * (CF Γ p).H L115 + (7 : ℝ) * (CF Γ p).H L169 + (-28 : ℝ) * (CF Γ p).H L30 + (-7 : ℝ) * (CF Γ p).H L451 := by
  have hL := lem_matus7 ((CF Γ p).lsp ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L11 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1363 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1364 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1365 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1366 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1367 from rfl, show ([1] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L98 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L478 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1368 from rfl, show ([2] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L31 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L219, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1369 from rfl] at hL
  rw [i6 h, i921 h, i922 h, i923 h, i924 h, i925 h, i48 h, i251 h, i926 h, i16 h, i927 h] at hL
  linarith

theorem row286 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-8 : ℝ) * (CF Γ p).H L10 + (36 : ℝ) * (CF Γ p).H L809 + (-64 : ℝ) * (CF Γ p).H L242 + (-7 : ℝ) * (CF Γ p).H L1038 + (36 : ℝ) * (CF Γ p).H L238 + (7 : ℝ) * (CF Γ p).H L244 + (-35 : ℝ) * (CF Γ p).H L97 + (63 : ℝ) * (CF Γ p).H L115 + (7 : ℝ) * (CF Γ p).H L1199 + (-28 : ℝ) * (CF Γ p).H L30 + (-7 : ℝ) * (CF Γ p).H L205 := by
  have hL := lem_matus7 ((CF Γ p).lsp ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L11 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1363 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1364 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1370 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1366 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1371 from rfl, show ([1] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L98 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L478 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1372 from rfl, show ([2] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L31 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L11, L98, L31, L76, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L206 from rfl] at hL
  rw [i6 h, i921 h, i922 h, i928 h, i924 h, i929 h, i48 h, i251 h, i930 h, i16 h, i100 h] at hL
  linarith

theorem row287 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-18 : ℝ) * (CF Γ p).H L800 + (171 : ℝ) * (CF Γ p).H L649 + (-324 : ℝ) * (CF Γ p).H L530 + (-17 : ℝ) * (CF Γ p).H L653 + (171 : ℝ) * (CF Γ p).H L804 + (17 : ℝ) * (CF Γ p).H L265 + (-170 : ℝ) * (CF Γ p).H L436 + (323 : ℝ) * (CF Γ p).H L413 + (17 : ℝ) * (CF Γ p).H L408 + (-153 : ℝ) * (CF Γ p).H L562 + (-17 : ℝ) * (CF Γ p).H L352 := by
  have hL := lem_matus17 ((CF Γ p).lsp ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L968 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1374 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1375 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1376 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1377 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1378 from rfl, show ([1] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1007 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1379 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1380 from rfl, show ([2] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1373 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L968, L1007, L1373, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1381 from rfl] at hL
  rw [i582 h, i931 h, i932 h, i933 h, i934 h, i935 h, i613 h, i936 h, i937 h, i938 h, i939 h] at hL
  linarith

theorem row288 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-11 : ℝ) * (CF Γ p).H L476 + (66 : ℝ) * (CF Γ p).H L917 + (-141 : ℝ) * (CF Γ p).H L545 + (66 : ℝ) * (CF Γ p).H L449 + (10 : ℝ) * (CF Γ p).H L432 + (-65 : ℝ) * (CF Γ p).H L809 + (120 : ℝ) * (CF Γ p).H L242 + (10 : ℝ) * (CF Γ p).H L1038 + (-55 : ℝ) * (CF Γ p).H L169 := by
  have hL := lem_matus10 ((CF Γ p).lsp ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L477 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1384 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1385 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1386 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1387 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1388 from rfl, show ([1] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L810 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1389 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1390 from rfl, show ([2] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1383 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L477, L810, L1383, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1391 from rfl] at hL
  rw [i250 h, i940 h, i941 h, i942 h, i943 h, i944 h, i473 h, i945 h, i946 h, i947 h, i948 h] at hL
  linarith

theorem row289 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-16 : ℝ) * (CF Γ p).H L430 + (136 : ℝ) * (CF Γ p).H L432 + (-256 : ℝ) * (CF Γ p).H L545 + (-15 : ℝ) * (CF Γ p).H L530 + (136 : ℝ) * (CF Γ p).H L246 + (15 : ℝ) * (CF Γ p).H L804 + (-135 : ℝ) * (CF Γ p).H L484 + (255 : ℝ) * (CF Γ p).H L486 + (15 : ℝ) * (CF Γ p).H L831 + (-120 : ℝ) * (CF Γ p).H L575 + (-15 : ℝ) * (CF Γ p).H L524 := by
  have hL := lem_matus15 ((CF Γ p).lsp ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1393 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1395 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1396 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1397 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1398 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1399 from rfl, show ([1] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1394 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1400 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1401 from rfl, show ([2] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L576 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1393, L1394, L576, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1402 from rfl] at hL
  rw [i949 h, i950 h, i951 h, i952 h, i953 h, i954 h, i955 h, i956 h, i957 h, i311 h, i958 h] at hL
  linarith

theorem row290 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-63 : ℝ) * (CF Γ p).H L190 + (2016 : ℝ) * (CF Γ p).H L747 + (-4093 : ℝ) * (CF Γ p).H L311 + (2016 : ℝ) * (CF Γ p).H L379 + (62 : ℝ) * (CF Γ p).H L260 + (-2015 : ℝ) * (CF Γ p).H L612 + (3968 : ℝ) * (CF Γ p).H L741 + (62 : ℝ) * (CF Γ p).H L758 + (-1953 : ℝ) * (CF Γ p).H L77 := by
  have hL := lem_matus62 ((CF Γ p).lsp ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L191 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1405 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1406 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1407 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1408 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1409 from rfl, show ([1] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L613 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1410 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1411 from rfl, show ([2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1404 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1412 from rfl] at hL
  rw [i93 h, i959 h, i960 h, i961 h, i962 h, i963 h, i334 h, i964 h, i965 h, i966 h, i967 h] at hL
  linarith

theorem row291 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-58 : ℝ) * (CF Γ p).H L190 + (1711 : ℝ) * (CF Γ p).H L747 + (-3478 : ℝ) * (CF Γ p).H L311 + (1711 : ℝ) * (CF Γ p).H L379 + (57 : ℝ) * (CF Γ p).H L260 + (-1710 : ℝ) * (CF Γ p).H L612 + (3363 : ℝ) * (CF Γ p).H L741 + (57 : ℝ) * (CF Γ p).H L758 + (-1653 : ℝ) * (CF Γ p).H L77 := by
  have hL := lem_matus57 ((CF Γ p).lsp ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L191 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1405 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1406 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1407 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1408 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1409 from rfl, show ([1] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L613 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1410 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1411 from rfl, show ([2] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1404 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L191, L613, L1404, L210, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1412 from rfl] at hL
  rw [i93 h, i959 h, i960 h, i961 h, i962 h, i963 h, i334 h, i964 h, i965 h, i966 h, i967 h] at hL
  linarith

theorem row292 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (-17 : ℝ) * (CF Γ p).H L383 + (153 : ℝ) * (CF Γ p).H L645 + (-289 : ℝ) * (CF Γ p).H L657 + (-16 : ℝ) * (CF Γ p).H L608 + (153 : ℝ) * (CF Γ p).H L570 + (16 : ℝ) * (CF Γ p).H L1046 + (-152 : ℝ) * (CF Γ p).H L436 + (288 : ℝ) * (CF Γ p).H L408 + (16 : ℝ) * (CF Γ p).H L413 + (-136 : ℝ) * (CF Γ p).H L560 + (-16 : ℝ) * (CF Γ p).H L352 := by
  have hL := lem_matus16 ((CF Γ p).lsp ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1036 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1414 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1415 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1416 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1417 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1418 from rfl, show ([1] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1007 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1419 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1420 from rfl, show ([2] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L655 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1036, L1007, L655, L122, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1421 from rfl] at hL
  rw [i639 h, i968 h, i969 h, i970 h, i971 h, i972 h, i613 h, i973 h, i974 h, i359 h, i975 h] at hL
  linarith

theorem row293 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L105 + (-1 : ℝ) * (CF Γ p).H L22 = 0 := by
  have hh : (C1 Γ p).H (L106 ++ ([] : List (Form 6))) = (C1 Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L106 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L106 ++ ([] : List (Form 6)) = L106 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  rw [← lift1 h L23 (by decide) (by decide), ← lift1 h L106 (by decide) (by decide)] at hh
  rw [i12 h, i52 h] at hh
  linarith

theorem row294 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L42 + (-1 : ℝ) * (CF Γ p).H L38 = 0 := by
  have hh : (C1 Γ p).H (L43 ++ ([] : List (Form 6))) = (C1 Γ p).H (L39 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L43 ([] : List (Form 6)) L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L43 ++ ([] : List (Form 6)) = L43 from rfl, show L39 ++ ([] : List (Form 6)) = L39 from rfl] at hh
  rw [← lift1 h L39 (by decide) (by decide), ← lift1 h L43 (by decide) (by decide)] at hh
  rw [i20 h, i22 h] at hh
  linarith

theorem row295 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L1097 + (-1 : ℝ) * (CF Γ p).H L314 = 0 := by
  have hh : (C1 Γ p).H (L1423 ++ ([] : List (Form 6))) = (C1 Γ p).H (L315 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L1423 ([] : List (Form 6)) L315 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1423 ++ ([] : List (Form 6)) = L1423 from rfl, show L315 ++ ([] : List (Form 6)) = L315 from rfl] at hh
  rw [← lift1 h L315 (by decide) (by decide), ← lift1 h L1423 (by decide) (by decide)] at hh
  rw [i152 h, i976 h] at hh
  linarith

theorem row296 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L10 + (-1 : ℝ) * (CF Γ p).H L16 = 0 := by
  have hh : (C2 Γ p).H (L11 ++ ([] : List (Form 6))) = (C2 Γ p).H (L17 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L11 ([] : List (Form 6)) L17 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L11 ++ ([] : List (Form 6)) = L11 from rfl, show L17 ++ ([] : List (Form 6)) = L17 from rfl] at hh
  rw [← lift2 h L17 (by decide), ← lift2 h L11 (by decide)] at hh
  rw [i9 h, i6 h] at hh
  linarith

theorem row297 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L26 + (-1 : ℝ) * (CF Γ p).H L38 = 0 := by
  have hh : (C2 Γ p).H (L27 ++ ([] : List (Form 6))) = (C2 Γ p).H (L39 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L27 ([] : List (Form 6)) L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L27 ++ ([] : List (Form 6)) = L27 from rfl, show L39 ++ ([] : List (Form 6)) = L39 from rfl] at hh
  rw [← lift2 h L39 (by decide), ← lift2 h L27 (by decide)] at hh
  rw [i20 h, i14 h] at hh
  linarith

theorem row298 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L602 + (-1 : ℝ) * (CF Γ p).H L314 = 0 := by
  have hh : (C2 Γ p).H (L603 ++ ([] : List (Form 6))) = (C2 Γ p).H (L315 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L603 ([] : List (Form 6)) L315 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L603 ++ ([] : List (Form 6)) = L603 from rfl, show L315 ++ ([] : List (Form 6)) = L315 from rfl] at hh
  rw [← lift2 h L315 (by decide), ← lift2 h L603 (by decide)] at hh
  rw [i152 h, i328 h] at hh
  linarith

theorem row299 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L30 + (-1 : ℝ) * (CF Γ p).H L42 = 0 := by
  have hh : (C2 Γ p).H (L31 ++ ([] : List (Form 6))) = (C2 Γ p).H (L43 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L31 ([] : List (Form 6)) L43 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L31 ++ ([] : List (Form 6)) = L31 from rfl, show L43 ++ ([] : List (Form 6)) = L43 from rfl] at hh
  rw [← lift2 h L43 (by decide), ← lift2 h L31 (by decide)] at hh
  rw [i22 h, i16 h] at hh
  linarith

end EntropyBounds.Glue.Certs.CL3B6SC
