import EntropyBounds.GlueG.Certs.CL3B6SC.Ids0
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids1
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids2
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids3
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids4
import EntropyBounds.Glue.Certs.CL3B6SC.Lemmas
import EntropyBounds.GlueG.Lemma

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.GlueG.Certs.CL3B6SC

open EntropyBounds.Glue.Certs.CL3B6SC

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG SumsDifferences SumsDifferences.NonShannon
open EntropyBounds.Lem

theorem row150 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L107 + (-1 : ℝ) * (CF Γ p).H L578 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L62 [F4]
  rw [show [F22] ++ L62 ++ [F4] = L579 from rfl, show [F22] ++ L62 = L573 from rfl,
    show L62 ++ [F4] = L577 from rfl] at hh
  rw [i296 h, i292 h, i295 h] at hh
  linarith

theorem row151 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L580 + (-1 : ℝ) * (CF Γ p).H L581 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L62 [F54]
  rw [show [F22] ++ L62 ++ [F54] = L582 from rfl, show [F22] ++ L62 = L573 from rfl,
    show L62 ++ [F54] = L580 from rfl] at hh
  rw [i297 h, i292 h] at hh
  linarith

theorem row152 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L583 + (-1 : ℝ) * (CF Γ p).H L584 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L62 [F53]
  rw [show [F22] ++ L62 ++ [F53] = L585 from rfl, show [F22] ++ L62 = L573 from rfl,
    show L62 ++ [F53] = L583 from rfl] at hh
  rw [i298 h, i292 h] at hh
  linarith

theorem row153 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L578 + (1 : ℝ) * (CF Γ p).H L588 + (-1 : ℝ) * (CF Γ p).H L591 + (-1 : ℝ) * (CF Γ p).H L320 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L321 [F15]
  rw [show [F22] ++ L321 ++ [F15] = L592 from rfl, show [F22] ++ L321 = L586 from rfl,
    show L321 ++ [F15] = L589 from rfl] at hh
  rw [i301 h, i299 h, i300 h, i137 h] at hh
  linarith

theorem row154 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L156 + (1 : ℝ) * (CF Γ p).H L80 + (-1 : ℝ) * (CF Γ p).H L596 + (-1 : ℝ) * (CF Γ p).H L179 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L179 [F15]
  rw [show [F22] ++ L179 ++ [F15] = L597 from rfl, show [F22] ++ L179 = L594 from rfl,
    show L179 ++ [F15] = L595 from rfl] at hh
  rw [i304 h, i302 h, i303 h] at hh
  linarith

theorem row155 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L598 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L600 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L65 [F17]
  rw [show [F22] ++ L65 ++ [F17] = L601 from rfl, show [F22] ++ L65 = L599 from rfl,
    show L65 ++ [F17] = L336 from rfl] at hh
  rw [i306 h, i305 h, i147 h] at hh
  linarith

theorem row156 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L177 + (1 : ℝ) * (CF Γ p).H L98 + (-1 : ℝ) * (CF Γ p).H L604 + (-1 : ℝ) * (CF Γ p).H L77 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L77 [F11]
  rw [show [F22] ++ L77 ++ [F11] = L605 from rfl, show [F22] ++ L77 = L602 from rfl,
    show L77 ++ [F11] = L603 from rfl] at hh
  rw [i309 h, i307 h, i308 h] at hh
  linarith

theorem row157 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L366 + (1 : ℝ) * (CF Γ p).H L224 + (-1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L517 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L610 [F15]
  rw [show [F44] ++ L610 ++ [F15] = L609 from rfl, show [F44] ++ L610 = L606 from rfl,
    show L610 ++ [F15] = L607 from rfl] at hh
  rw [i312 h, i310 h, i311 h, i313 h] at hh
  linarith

theorem row158 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L366 + (1 : ℝ) * (CF Γ p).H L527 + (-1 : ℝ) * (CF Γ p).H L612 + (-1 : ℝ) * (CF Γ p).H L517 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L610 [F17]
  rw [show [F44] ++ L610 ++ [F17] = L613 from rfl, show [F44] ++ L610 = L606 from rfl,
    show L610 ++ [F17] = L611 from rfl] at hh
  rw [i315 h, i310 h, i314 h, i313 h] at hh
  linarith

theorem row159 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L357 + (1 : ℝ) * (CF Γ p).H L195 + (-1 : ℝ) * (CF Γ p).H L334 + (-1 : ℝ) * (CF Γ p).H L355 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L617 [F17]
  rw [show [F44] ++ L617 ++ [F17] = L616 from rfl, show [F44] ++ L617 = L614 from rfl,
    show L617 ++ [F17] = L615 from rfl] at hh
  rw [i318 h, i316 h, i317 h, i319 h] at hh
  linarith

theorem row160 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L15 + (1 : ℝ) * (CF Γ p).H L147 + (-1 : ℝ) * (CF Γ p).H L165 + (-1 : ℝ) * (CF Γ p).H L109 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L109 [F11]
  rw [show [F15] ++ L109 ++ [F11] = L620 from rfl, show [F15] ++ L109 = L618 from rfl,
    show L109 ++ [F11] = L619 from rfl] at hh
  rw [i322 h, i320 h, i321 h] at hh
  linarith

theorem row161 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L15 + (1 : ℝ) * (CF Γ p).H L113 + (-1 : ℝ) * (CF Γ p).H L588 + (-1 : ℝ) * (CF Γ p).H L164 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L164 [F4]
  rw [show [F15] ++ L164 ++ [F4] = L622 from rfl, show [F15] ++ L164 = L621 from rfl,
    show L164 ++ [F4] = L529 from rfl] at hh
  rw [i324 h, i323 h, i265 h] at hh
  linarith

theorem row162 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L241 + (1 : ℝ) * (CF Γ p).H L624 + (-1 : ℝ) * (CF Γ p).H L626 + (-1 : ℝ) * (CF Γ p).H L130 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L130 [F4]
  rw [show [F15] ++ L130 ++ [F4] = L627 from rfl, show [F15] ++ L130 = L623 from rfl,
    show L130 ++ [F4] = L625 from rfl] at hh
  rw [i327 h, i325 h, i326 h] at hh
  linarith

theorem row163 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L165 + (1 : ℝ) * (CF Γ p).H L314 + (-1 : ℝ) * (CF Γ p).H L473 + (-1 : ℝ) * (CF Γ p).H L297 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L631 [F58]
  rw [show [F18] ++ L631 ++ [F58] = L630 from rfl, show [F18] ++ L631 = L628 from rfl,
    show L631 ++ [F58] = L629 from rfl] at hh
  rw [i330 h, i328 h, i329 h, i331 h] at hh
  linarith

theorem row164 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L69 + (1 : ℝ) * (CF Γ p).H L162 + (-1 : ℝ) * (CF Γ p).H L634 + (-1 : ℝ) * (CF Γ p).H L151 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L151 [F3]
  rw [show [F15] ++ L151 ++ [F3] = L635 from rfl, show [F15] ++ L151 = L632 from rfl,
    show L151 ++ [F3] = L633 from rfl] at hh
  rw [i334 h, i332 h, i333 h] at hh
  linarith

theorem row165 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L72 + (1 : ℝ) * (CF Γ p).H L145 + (-1 : ℝ) * (CF Γ p).H L187 + (-1 : ℝ) * (CF Γ p).H L223 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L223 [F17]
  rw [show [F15] ++ L223 ++ [F17] = L638 from rfl, show [F15] ++ L223 = L636 from rfl,
    show L223 ++ [F17] = L637 from rfl] at hh
  rw [i337 h, i335 h, i336 h] at hh
  linarith

theorem row166 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L549 + (1 : ℝ) * (CF Γ p).H L640 + (-1 : ℝ) * (CF Γ p).H L642 + (-1 : ℝ) * (CF Γ p).H L176 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L176 [F54]
  rw [show [F17] ++ L176 ++ [F54] = L643 from rfl, show [F17] ++ L176 = L639 from rfl,
    show L176 ++ [F54] = L641 from rfl] at hh
  rw [i340 h, i338 h, i339 h] at hh
  linarith

theorem row167 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L96 + (1 : ℝ) * (CF Γ p).H L210 + (-1 : ℝ) * (CF Γ p).H L236 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L65 [F6]
  rw [show [F17] ++ L65 ++ [F6] = L646 from rfl, show [F17] ++ L65 = L644 from rfl,
    show L65 ++ [F6] = L645 from rfl] at hh
  rw [i343 h, i341 h, i342 h] at hh
  linarith

theorem row168 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L96 + (1 : ℝ) * (CF Γ p).H L647 + (-1 : ℝ) * (CF Γ p).H L563 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L65 [F3]
  rw [show [F17] ++ L65 ++ [F3] = L649 from rfl, show [F17] ++ L65 = L644 from rfl,
    show L65 ++ [F3] = L648 from rfl] at hh
  rw [i345 h, i341 h, i344 h] at hh
  linarith

theorem row169 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L96 + (1 : ℝ) * (CF Γ p).H L650 + (-1 : ℝ) * (CF Γ p).H L270 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L65 [F47]
  rw [show [F17] ++ L65 ++ [F47] = L651 from rfl, show [F17] ++ L65 = L644 from rfl,
    show L65 ++ [F47] = L650 from rfl] at hh
  rw [i346 h, i341 h] at hh
  linarith

theorem row170 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L236 + (1 : ℝ) * (CF Γ p).H L195 + (-1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L549 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L550 [F18]
  rw [show [F58] ++ L550 ++ [F18] = L655 from rfl, show [F58] ++ L550 = L653 from rfl,
    show L550 ++ [F18] = L654 from rfl] at hh
  rw [i349 h, i347 h, i348 h, i279 h] at hh
  linarith

theorem row171 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L195 + (1 : ℝ) * (CF Γ p).H L224 + (-1 : ℝ) * (CF Γ p).H L494 + (-1 : ℝ) * (CF Γ p).H L355 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L617 [F15]
  rw [show [F17] ++ L617 ++ [F15] = L658 from rfl, show [F17] ++ L617 = L656 from rfl,
    show L617 ++ [F15] = L657 from rfl] at hh
  rw [i352 h, i350 h, i351 h, i319 h] at hh
  linarith

theorem row172 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L195 + (1 : ℝ) * (CF Γ p).H L660 + (-1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L663 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L664 [F58]
  rw [show [F18] ++ L664 ++ [F58] = L662 from rfl, show [F18] ++ L664 = L659 from rfl,
    show L664 ++ [F58] = L661 from rfl] at hh
  rw [i355 h, i353 h, i354 h, i356 h] at hh
  linarith

theorem row173 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L158 + (1 : ℝ) * (CF Γ p).H L666 + (-1 : ℝ) * (CF Γ p).H L668 + (-1 : ℝ) * (CF Γ p).H L164 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L164 [F52]
  rw [show [F17] ++ L164 ++ [F52] = L669 from rfl, show [F17] ++ L164 = L665 from rfl,
    show L164 ++ [F52] = L667 from rfl] at hh
  rw [i359 h, i357 h, i358 h] at hh
  linarith

theorem row174 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L670 + (1 : ℝ) * (CF Γ p).H L170 + (-1 : ℝ) * (CF Γ p).H L672 + (-1 : ℝ) * (CF Γ p).H L122 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L122 [F3]
  rw [show [F17] ++ L122 ++ [F3] = L673 from rfl, show [F17] ++ L122 = L671 from rfl,
    show L122 ++ [F3] = L417 from rfl] at hh
  rw [i361 h, i360 h, i196 h] at hh
  linarith

theorem row175 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L341 + (1 : ℝ) * (CF Γ p).H L297 + (-1 : ℝ) * (CF Γ p).H L676 + (-1 : ℝ) * (CF Γ p).H L130 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L130 [F11]
  rw [show [F17] ++ L130 ++ [F11] = L677 from rfl, show [F17] ++ L130 = L674 from rfl,
    show L130 ++ [F11] = L675 from rfl] at hh
  rw [i364 h, i362 h, i363 h] at hh
  linarith

theorem row176 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L678 + (1 : ℝ) * (CF Γ p).H L160 + (-1 : ℝ) * (CF Γ p).H L494 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L186 [F11]
  rw [show [F17] ++ L186 ++ [F11] = L680 from rfl, show [F17] ++ L186 = L678 from rfl,
    show L186 ++ [F11] = L679 from rfl] at hh
  rw [i366 h, i365 h] at hh
  linarith

theorem row177 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L193 + (1 : ℝ) * (CF Γ p).H L98 + (-1 : ℝ) * (CF Γ p).H L682 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] L82 [F11]
  rw [show [F17] ++ L82 ++ [F11] = L683 from rfl, show [F17] ++ L82 = L193 from rfl,
    show L82 ++ [F11] = L435 from rfl] at hh
  rw [i367 h, i207 h] at hh
  linarith

theorem row178 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L123 + (1 : ℝ) * (CF Γ p).H L202 + (-1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L200 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L201 [F18]
  rw [show [F29] ++ L201 ++ [F18] = L686 from rfl, show [F29] ++ L201 = L684 from rfl,
    show L201 ++ [F18] = L685 from rfl] at hh
  rw [i370 h, i368 h, i369 h, i75 h] at hh
  linarith

theorem row179 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L123 + (1 : ℝ) * (CF Γ p).H L672 + (-1 : ℝ) * (CF Γ p).H L565 + (-1 : ℝ) * (CF Γ p).H L670 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L690 [F3]
  rw [show [F29] ++ L690 ++ [F3] = L689 from rfl, show [F29] ++ L690 = L687 from rfl,
    show L690 ++ [F3] = L688 from rfl] at hh
  rw [i373 h, i371 h, i372 h, i374 h] at hh
  linarith

theorem row180 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L270 + (1 : ℝ) * (CF Γ p).H L302 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L694 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L695 [F18]
  rw [show [F29] ++ L695 ++ [F18] = L693 from rfl, show [F29] ++ L695 = L691 from rfl,
    show L695 ++ [F18] = L692 from rfl] at hh
  rw [i377 h, i375 h, i376 h, i378 h] at hh
  linarith

theorem row181 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L270 + (1 : ℝ) * (CF Γ p).H L697 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L700 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L701 [F18]
  rw [show [F44] ++ L701 ++ [F18] = L699 from rfl, show [F44] ++ L701 = L696 from rfl,
    show L701 ++ [F18] = L698 from rfl] at hh
  rw [i381 h, i379 h, i380 h, i382 h] at hh
  linarith

theorem row182 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L270 + (1 : ℝ) * (CF Γ p).H L703 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L464 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L706 [F22]
  rw [show [F44] ++ L706 ++ [F22] = L705 from rfl, show [F44] ++ L706 = L702 from rfl,
    show L706 ++ [F22] = L704 from rfl] at hh
  rw [i385 h, i383 h, i384 h, i386 h] at hh
  linarith

theorem row183 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L270 + (1 : ℝ) * (CF Γ p).H L708 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L711 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L712 [F18]
  rw [show [F44] ++ L712 ++ [F18] = L710 from rfl, show [F44] ++ L712 = L707 from rfl,
    show L712 ++ [F18] = L709 from rfl] at hh
  rw [i389 h, i387 h, i388 h, i390 h] at hh
  linarith

theorem row184 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L187 + (1 : ℝ) * (CF Γ p).H L714 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L420 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L428 [F45]
  rw [show [F15] ++ L428 ++ [F45] = L716 from rfl, show [F15] ++ L428 = L713 from rfl,
    show L428 ++ [F45] = L715 from rfl] at hh
  rw [i393 h, i391 h, i392 h, i203 h] at hh
  linarith

theorem row185 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L187 + (1 : ℝ) * (CF Γ p).H L719 + (-1 : ℝ) * (CF Γ p).H L721 + (-1 : ℝ) * (CF Γ p).H L678 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L678 [F58]
  rw [show [F29] ++ L678 ++ [F58] = L722 from rfl, show [F29] ++ L678 = L718 from rfl,
    show L678 ++ [F58] = L720 from rfl] at hh
  rw [i396 h, i394 h, i395 h] at hh
  linarith

theorem row186 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L494 + (1 : ℝ) * (CF Γ p).H L591 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L726 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L727 [F58]
  rw [show [F29] ++ L727 ++ [F58] = L725 from rfl, show [F29] ++ L727 = L723 from rfl,
    show L727 ++ [F58] = L724 from rfl] at hh
  rw [i399 h, i397 h, i398 h, i400 h] at hh
  linarith

theorem row187 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L494 + (1 : ℝ) * (CF Γ p).H L729 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L634 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L732 [F44]
  rw [show [F29] ++ L732 ++ [F44] = L731 from rfl, show [F29] ++ L732 = L728 from rfl,
    show L732 ++ [F44] = L730 from rfl] at hh
  rw [i403 h, i401 h, i402 h, i404 h] at hh
  linarith

theorem row188 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L98 + (1 : ℝ) * (CF Γ p).H L75 + (-1 : ℝ) * (CF Γ p).H L314 + (-1 : ℝ) * (CF Γ p).H L77 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L77 [F6]
  rw [show [F11] ++ L77 ++ [F6] = L735 from rfl, show [F11] ++ L77 = L733 from rfl,
    show L77 ++ [F6] = L734 from rfl] at hh
  rw [i407 h, i405 h, i406 h] at hh
  linarith

theorem row189 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L98 + (1 : ℝ) * (CF Γ p).H L192 + (-1 : ℝ) * (CF Γ p).H L737 + (-1 : ℝ) * (CF Γ p).H L77 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L77 [F3]
  rw [show [F11] ++ L77 ++ [F3] = L738 from rfl, show [F11] ++ L77 = L733 from rfl,
    show L77 ++ [F3] = L736 from rfl] at hh
  rw [i409 h, i405 h, i408 h] at hh
  linarith

theorem row190 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L98 + (1 : ℝ) * (CF Γ p).H L740 + (-1 : ℝ) * (CF Γ p).H L742 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L82 [F49]
  rw [show [F11] ++ L82 ++ [F49] = L743 from rfl, show [F11] ++ L82 = L739 from rfl,
    show L82 ++ [F49] = L741 from rfl] at hh
  rw [i412 h, i410 h, i411 h] at hh
  linarith

theorem row191 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L160 + (1 : ℝ) * (CF Γ p).H L745 + (-1 : ℝ) * (CF Γ p).H L747 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L186 [F37]
  rw [show [F11] ++ L186 ++ [F37] = L748 from rfl, show [F11] ++ L186 = L744 from rfl,
    show L186 ++ [F37] = L746 from rfl] at hh
  rw [i415 h, i413 h, i414 h] at hh
  linarith

theorem row192 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L172 + (1 : ℝ) * (CF Γ p).H L750 + (-1 : ℝ) * (CF Γ p).H L747 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L62 [F28]
  rw [show [F11] ++ L62 ++ [F28] = L752 from rfl, show [F11] ++ L62 = L749 from rfl,
    show L62 ++ [F28] = L751 from rfl] at hh
  rw [i418 h, i416 h, i417 h] at hh
  linarith

theorem row193 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L753 + (1 : ℝ) * (CF Γ p).H L755 + (-1 : ℝ) * (CF Γ p).H L757 + (-1 : ℝ) * (CF Γ p).H L176 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L176 [F43]
  rw [show [F11] ++ L176 ++ [F43] = L758 from rfl, show [F11] ++ L176 = L754 from rfl,
    show L176 ++ [F43] = L756 from rfl] at hh
  rw [i421 h, i419 h, i420 h] at hh
  linarith

theorem row194 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L202 + (1 : ℝ) * (CF Γ p).H L352 + (-1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L762 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L763 [F44]
  rw [show [F18] ++ L763 ++ [F44] = L761 from rfl, show [F18] ++ L763 = L759 from rfl,
    show L763 ++ [F44] = L760 from rfl] at hh
  rw [i424 h, i422 h, i423 h, i425 h] at hh
  linarith

theorem row195 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L202 + (1 : ℝ) * (CF Γ p).H L414 + (-1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L413 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L413 [F29]
  rw [show [F18] ++ L413 ++ [F29] = L766 from rfl, show [F18] ++ L413 = L764 from rfl,
    show L413 ++ [F29] = L765 from rfl] at hh
  rw [i428 h, i426 h, i427 h] at hh
  linarith

theorem row196 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L224 + (1 : ℝ) * (CF Γ p).H L248 + (-1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L770 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L771 [F44]
  rw [show [F18] ++ L771 ++ [F44] = L769 from rfl, show [F18] ++ L771 = L767 from rfl,
    show L771 ++ [F44] = L768 from rfl] at hh
  rw [i431 h, i429 h, i430 h, i432 h] at hh
  linarith

theorem row197 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L210 + (1 : ℝ) * (CF Γ p).H L772 + (-1 : ℝ) * (CF Γ p).H L774 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L100 [F54]
  rw [show [F6] ++ L100 ++ [F54] = L775 from rfl, show [F6] ++ L100 = L211 from rfl,
    show L100 ++ [F54] = L773 from rfl] at hh
  rw [i434 h, i80 h, i433 h] at hh
  linarith

theorem row198 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L45 + (1 : ℝ) * (CF Γ p).H L777 + (-1 : ℝ) * (CF Γ p).H L556 + (-1 : ℝ) * (CF Γ p).H L179 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L179 [F52]
  rw [show [F6] ++ L179 ++ [F52] = L779 from rfl, show [F6] ++ L179 = L776 from rfl,
    show L179 ++ [F52] = L778 from rfl] at hh
  rw [i437 h, i435 h, i436 h] at hh
  linarith

theorem row199 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L246 + (1 : ℝ) * (CF Γ p).H L782 + (-1 : ℝ) * (CF Γ p).H L784 + (-1 : ℝ) * (CF Γ p).H L176 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] L176 [F3]
  rw [show [F4] ++ L176 ++ [F3] = L785 from rfl, show [F4] ++ L176 = L781 from rfl,
    show L176 ++ [F3] = L783 from rfl] at hh
  rw [i440 h, i438 h, i439 h] at hh
  linarith

theorem row200 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L786 + (1 : ℝ) * (CF Γ p).H L788 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L544 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L792 [F18]
  rw [show [F58] ++ L792 ++ [F18] = L790 from rfl, show [F58] ++ L792 = L787 from rfl,
    show L792 ++ [F18] = L789 from rfl] at hh
  rw [i443 h, i441 h, i442 h, i444 h] at hh
  linarith

theorem row201 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L212 + (1 : ℝ) * (CF Γ p).H L443 + (-1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L532 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L533 [F17]
  rw [show [F6] ++ L533 ++ [F17] = L794 from rfl, show [F6] ++ L533 = L793 from rfl,
    show L533 ++ [F17] = L534 from rfl] at hh
  rw [i446 h, i445 h, i268 h, i267 h] at hh
  linarith

theorem row202 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L233 + (1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L797 + (-1 : ℝ) * (CF Γ p).H L346 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L799 [F29]
  rw [show [F18] ++ L799 ++ [F29] = L798 from rfl, show [F18] ++ L799 = L795 from rfl,
    show L799 ++ [F29] = L796 from rfl] at hh
  rw [i449 h, i447 h, i448 h, i450 h] at hh
  linarith

theorem row203 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L694 + (1 : ℝ) * (CF Γ p).H L801 + (-1 : ℝ) * (CF Γ p).H L803 + (-1 : ℝ) * (CF Γ p).H L569 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L570 [F55]
  rw [show [F44] ++ L570 ++ [F55] = L804 from rfl, show [F44] ++ L570 = L800 from rfl,
    show L570 ++ [F55] = L802 from rfl] at hh
  rw [i453 h, i451 h, i452 h, i290 h] at hh
  linarith

theorem row204 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L694 + (1 : ℝ) * (CF Γ p).H L806 + (-1 : ℝ) * (CF Γ p).H L808 + (-1 : ℝ) * (CF Γ p).H L650 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L810 [F31]
  rw [show [F44] ++ L810 ++ [F31] = L809 from rfl, show [F44] ++ L810 = L805 from rfl,
    show L810 ++ [F31] = L807 from rfl] at hh
  rw [i456 h, i454 h, i455 h, i457 h] at hh
  linarith

theorem row205 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L248 + (1 : ℝ) * (CF Γ p).H L348 + (-1 : ℝ) * (CF Γ p).H L729 + (-1 : ℝ) * (CF Γ p).H L344 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L814 [F3]
  rw [show [F15] ++ L814 ++ [F3] = L813 from rfl, show [F15] ++ L814 = L811 from rfl,
    show L814 ++ [F3] = L812 from rfl] at hh
  rw [i460 h, i458 h, i459 h, i461 h] at hh
  linarith

theorem row206 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L248 + (1 : ℝ) * (CF Γ p).H L626 + (-1 : ℝ) * (CF Γ p).H L729 + (-1 : ℝ) * (CF Γ p).H L200 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L201 [F3]
  rw [show [F44] ++ L201 ++ [F3] = L817 from rfl, show [F44] ++ L201 = L815 from rfl,
    show L201 ++ [F3] = L816 from rfl] at hh
  rw [i464 h, i462 h, i463 h, i75 h] at hh
  linarith

theorem row207 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L243 + (1 : ℝ) * (CF Γ p).H L575 + (-1 : ℝ) * (CF Γ p).H L302 + (-1 : ℝ) * (CF Γ p).H L429 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L821 [F22]
  rw [show [F44] ++ L821 ++ [F22] = L820 from rfl, show [F44] ++ L821 = L818 from rfl,
    show L821 ++ [F22] = L819 from rfl] at hh
  rw [i467 h, i465 h, i466 h, i468 h] at hh
  linarith

theorem row208 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L302 + (1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L206 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L828 [F29]
  rw [show [F44] ++ L828 ++ [F29] = L826 from rfl, show [F44] ++ L828 = L822 from rfl,
    show L828 ++ [F29] = L824 from rfl] at hh
  rw [i471 h, i469 h, i470 h, i472 h] at hh
  linarith

theorem row209 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L302 + (1 : ℝ) * (CF Γ p).H L797 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L788 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L836 [F29]
  rw [show [F44] ++ L836 ++ [F29] = L834 from rfl, show [F44] ++ L836 = L830 from rfl,
    show L836 ++ [F29] = L832 from rfl] at hh
  rw [i475 h, i473 h, i474 h, i476 h] at hh
  linarith

theorem row210 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L302 + (1 : ℝ) * (CF Γ p).H L565 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L841 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L842 [F29]
  rw [show [F44] ++ L842 ++ [F29] = L840 from rfl, show [F44] ++ L842 = L838 from rfl,
    show L842 ++ [F29] = L839 from rfl] at hh
  rw [i479 h, i477 h, i478 h, i480 h] at hh
  linarith

theorem row211 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L352 + (1 : ℝ) * (CF Γ p).H L460 + (-1 : ℝ) * (CF Γ p).H L721 + (-1 : ℝ) * (CF Γ p).H L772 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L773 [F58]
  rw [show [F44] ++ L773 ++ [F58] = L845 from rfl, show [F44] ++ L773 = L843 from rfl,
    show L773 ++ [F58] = L844 from rfl] at hh
  rw [i483 h, i481 h, i482 h, i433 h] at hh
  linarith

theorem row212 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L294 + (1 : ℝ) * (CF Γ p).H L403 + (-1 : ℝ) * (CF Γ p).H L270 + (-1 : ℝ) * (CF Γ p).H L755 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L849 [F29]
  rw [show [F44] ++ L849 ++ [F29] = L848 from rfl, show [F44] ++ L849 = L846 from rfl,
    show L849 ++ [F29] = L847 from rfl] at hh
  rw [i486 h, i484 h, i485 h, i487 h] at hh
  linarith

theorem row213 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L294 + (1 : ℝ) * (CF Γ p).H L676 + (-1 : ℝ) * (CF Γ p).H L508 + (-1 : ℝ) * (CF Γ p).H L549 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L550 [F11]
  rw [show [F44] ++ L550 ++ [F11] = L852 from rfl, show [F44] ++ L550 = L850 from rfl,
    show L550 ++ [F11] = L851 from rfl] at hh
  rw [i490 h, i488 h, i489 h, i279 h] at hh
  linarith

theorem row214 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L337 + (1 : ℝ) * (CF Γ p).H L747 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L857 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L858 [F11]
  rw [show [F44] ++ L858 ++ [F11] = L855 from rfl, show [F44] ++ L858 = L853 from rfl,
    show L858 ++ [F11] = L854 from rfl] at hh
  rw [i493 h, i491 h, i492 h, i494 h] at hh
  linarith

theorem row215 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L334 + (1 : ℝ) * (CF Γ p).H L487 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L862 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L863 [F29]
  rw [show [F44] ++ L863 ++ [F29] = L861 from rfl, show [F44] ++ L863 = L859 from rfl,
    show L863 ++ [F29] = L860 from rfl] at hh
  rw [i497 h, i495 h, i496 h, i498 h] at hh
  linarith

theorem row216 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L721 + (1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L870 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L871 [F18]
  rw [show [F44] ++ L871 ++ [F18] = L868 from rfl, show [F44] ++ L871 = L864 from rfl,
    show L871 ++ [F18] = L866 from rfl] at hh
  rw [i501 h, i499 h, i500 h, i502 h] at hh
  linarith

theorem row217 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L721 + (1 : ℝ) * (CF Γ p).H L874 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L877 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L878 [F22]
  rw [show [F44] ++ L878 ++ [F22] = L876 from rfl, show [F44] ++ L878 = L873 from rfl,
    show L878 ++ [F22] = L875 from rfl] at hh
  rw [i505 h, i503 h, i504 h, i506 h] at hh
  linarith

theorem row218 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L721 + (1 : ℝ) * (CF Γ p).H L880 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L883 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L884 [F22]
  rw [show [F44] ++ L884 ++ [F22] = L882 from rfl, show [F44] ++ L884 = L879 from rfl,
    show L884 ++ [F22] = L881 from rfl] at hh
  rw [i509 h, i507 h, i508 h, i510 h] at hh
  linarith

theorem row219 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L299 + (1 : ℝ) * (CF Γ p).H L886 + (-1 : ℝ) * (CF Γ p).H L888 + (-1 : ℝ) * (CF Γ p).H L890 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L891 [F26]
  rw [show [F44] ++ L891 ++ [F26] = L889 from rfl, show [F44] ++ L891 = L885 from rfl,
    show L891 ++ [F26] = L887 from rfl] at hh
  rw [i513 h, i511 h, i512 h, i514 h] at hh
  linarith

theorem row220 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L284 + (1 : ℝ) * (CF Γ p).H L668 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L896 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L897 [F17]
  rw [show [F44] ++ L897 ++ [F17] = L894 from rfl, show [F44] ++ L897 = L892 from rfl,
    show L897 ++ [F17] = L893 from rfl] at hh
  rw [i517 h, i515 h, i516 h, i518 h] at hh
  linarith

theorem row221 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L317 + (1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L660 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L904 [F18]
  rw [show [F44] ++ L904 ++ [F18] = L902 from rfl, show [F44] ++ L904 = L898 from rfl,
    show L904 ++ [F18] = L900 from rfl] at hh
  rw [i521 h, i519 h, i520 h, i522 h] at hh
  linarith

theorem row222 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L317 + (1 : ℝ) * (CF Γ p).H L591 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L786 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L912 [F22]
  rw [show [F44] ++ L912 ++ [F22] = L910 from rfl, show [F44] ++ L912 = L906 from rfl,
    show L912 ++ [F22] = L908 from rfl] at hh
  rw [i525 h, i523 h, i524 h, i526 h] at hh
  linarith

theorem row223 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L317 + (1 : ℝ) * (CF Γ p).H L2 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L714 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L917 [F18]
  rw [show [F44] ++ L917 ++ [F18] = L916 from rfl, show [F44] ++ L917 = L914 from rfl,
    show L917 ++ [F18] = L915 from rfl] at hh
  rw [i529 h, i527 h, i528 h, i530 h] at hh
  linarith

theorem row224 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L288 + (1 : ℝ) * (CF Γ p).H L676 + (-1 : ℝ) * (CF Γ p).H L508 + (-1 : ℝ) * (CF Γ p).H L753 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L921 [F17]
  rw [show [F44] ++ L921 ++ [F17] = L920 from rfl, show [F44] ++ L921 = L918 from rfl,
    show L921 ++ [F17] = L919 from rfl] at hh
  rw [i533 h, i531 h, i532 h, i534 h] at hh
  linarith

theorem row225 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L288 + (1 : ℝ) * (CF Γ p).H L642 + (-1 : ℝ) * (CF Γ p).H L508 + (-1 : ℝ) * (CF Γ p).H L640 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L641 [F17]
  rw [show [F44] ++ L641 ++ [F17] = L924 from rfl, show [F44] ++ L641 = L922 from rfl,
    show L641 ++ [F17] = L923 from rfl] at hh
  rw [i537 h, i535 h, i536 h, i339 h] at hh
  linarith

theorem row226 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L797 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L928 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L929 [F29]
  rw [show [F44] ++ L929 ++ [F29] = L927 from rfl, show [F44] ++ L929 = L925 from rfl,
    show L929 ++ [F29] = L926 from rfl] at hh
  rw [i540 h, i538 h, i539 h, i541 h] at hh
  linarith

theorem row227 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L537 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L933 [F58]
  rw [show [F44] ++ L933 ++ [F58] = L932 from rfl, show [F44] ++ L933 = L930 from rfl,
    show L933 ++ [F58] = L931 from rfl] at hh
  rw [i544 h, i542 h, i543 h, i545 h] at hh
  linarith

theorem row228 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L556 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L596 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L937 [F29]
  rw [show [F44] ++ L937 ++ [F29] = L936 from rfl, show [F44] ++ L937 = L934 from rfl,
    show L937 ++ [F29] = L935 from rfl] at hh
  rw [i548 h, i546 h, i547 h, i549 h] at hh
  linarith

theorem row229 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L608 + (1 : ℝ) * (CF Γ p).H L939 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L942 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L943 [F29]
  rw [show [F44] ++ L943 ++ [F29] = L941 from rfl, show [F44] ++ L943 = L938 from rfl,
    show L943 ++ [F29] = L940 from rfl] at hh
  rw [i552 h, i550 h, i551 h, i553 h] at hh
  linarith

theorem row230 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L944 + (1 : ℝ) * (CF Γ p).H L423 + (-1 : ℝ) * (CF Γ p).H L947 + (-1 : ℝ) * (CF Γ p).H L745 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L949 [F29]
  rw [show [F44] ++ L949 ++ [F29] = L948 from rfl, show [F44] ++ L949 = L945 from rfl,
    show L949 ++ [F29] = L946 from rfl] at hh
  rw [i556 h, i554 h, i555 h, i557 h] at hh
  linarith

theorem row231 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L950 + (1 : ℝ) * (CF Γ p).H L411 + (-1 : ℝ) * (CF Γ p).H L953 + (-1 : ℝ) * (CF Γ p).H L955 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L956 [F11]
  rw [show [F22] ++ L956 ++ [F11] = L954 from rfl, show [F22] ++ L956 = L951 from rfl,
    show L956 ++ [F11] = L952 from rfl] at hh
  rw [i560 h, i558 h, i559 h, i561 h] at hh
  linarith

theorem row232 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L371 + (1 : ℝ) * (CF Γ p).H L604 + (-1 : ℝ) * (CF Γ p).H L487 + (-1 : ℝ) * (CF Γ p).H L394 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L960 [F11]
  rw [show [F29] ++ L960 ++ [F11] = L959 from rfl, show [F29] ++ L960 = L957 from rfl,
    show L960 ++ [F11] = L958 from rfl] at hh
  rw [i564 h, i562 h, i563 h, i565 h] at hh
  linarith

theorem row233 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L423 + (1 : ℝ) * (CF Γ p).H L575 + (-1 : ℝ) * (CF Γ p).H L953 + (-1 : ℝ) * (CF Γ p).H L598 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L599 [F11]
  rw [show [F29] ++ L599 ++ [F11] = L963 from rfl, show [F29] ++ L599 = L961 from rfl,
    show L599 ++ [F11] = L962 from rfl] at hh
  rw [i568 h, i566 h, i567 h, i305 h] at hh
  linarith

theorem row234 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L947 + (1 : ℝ) * (CF Γ p).H L803 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L944 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L967 [F15]
  rw [show [F29] ++ L967 ++ [F15] = L966 from rfl, show [F29] ++ L967 = L964 from rfl,
    show L967 ++ [F15] = L965 from rfl] at hh
  rw [i571 h, i569 h, i570 h, i572 h] at hh
  linarith

theorem row235 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L390 + (1 : ℝ) * (CF Γ p).H L515 + (-1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L971 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L972 [F18]
  rw [show [F29] ++ L972 ++ [F18] = L970 from rfl, show [F29] ++ L972 = L968 from rfl,
    show L972 ++ [F18] = L969 from rfl] at hh
  rw [i575 h, i573 h, i574 h, i576 h] at hh
  linarith

theorem row236 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L426 + (1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L975 + (-1 : ℝ) * (CF Γ p).H L624 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L977 [F18]
  rw [show [F29] ++ L977 ++ [F18] = L976 from rfl, show [F29] ++ L977 = L973 from rfl,
    show L977 ++ [F18] = L974 from rfl] at hh
  rw [i579 h, i577 h, i578 h, i580 h] at hh
  linarith

theorem row237 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L399 + (1 : ℝ) * (CF Γ p).H L742 + (-1 : ℝ) * (CF Γ p).H L487 + (-1 : ℝ) * (CF Γ p).H L740 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L740 [F11]
  rw [show [F29] ++ L740 ++ [F11] = L980 from rfl, show [F29] ++ L740 = L978 from rfl,
    show L740 ++ [F11] = L979 from rfl] at hh
  rw [i583 h, i581 h, i582 h] at hh
  linarith

theorem row238 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L448 + (1 : ℝ) * (CF Γ p).H L982 + (-1 : ℝ) * (CF Γ p).H L703 + (-1 : ℝ) * (CF Γ p).H L468 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L548 [F3]
  rw [show [F58] ++ L548 ++ [F3] = L984 from rfl, show [F58] ++ L548 = L981 from rfl,
    show L548 ++ [F3] = L983 from rfl] at hh
  rw [i586 h, i584 h, i585 h, i278 h] at hh
  linarith

theorem row239 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L877 + (1 : ℝ) * (CF Γ p).H L527 + (-1 : ℝ) * (CF Γ p).H L697 + (-1 : ℝ) * (CF Γ p).H L341 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L988 [F18]
  rw [show [F58] ++ L988 ++ [F18] = L987 from rfl, show [F58] ++ L988 = L985 from rfl,
    show L988 ++ [F18] = L986 from rfl] at hh
  rw [i589 h, i587 h, i588 h, i590 h] at hh
  linarith

theorem row240 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L443 + (1 : ℝ) * (CF Γ p).H L990 + (-1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L450 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L993 [F15]
  rw [show [F18] ++ L993 ++ [F15] = L992 from rfl, show [F18] ++ L993 = L989 from rfl,
    show L993 ++ [F15] = L991 from rfl] at hh
  rw [i593 h, i591 h, i592 h, i594 h] at hh
  linarith

theorem row241 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L530 + (1 : ℝ) * (CF Γ p).H L883 + (-1 : ℝ) * (CF Γ p).H L708 + (-1 : ℝ) * (CF Γ p).H L258 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L259 [F42]
  rw [show [F18] ++ L259 ++ [F42] = L996 from rfl, show [F18] ++ L259 = L994 from rfl,
    show L259 ++ [F42] = L995 from rfl] at hh
  rw [i597 h, i595 h, i596 h, i102 h] at hh
  linarith

theorem row242 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L928 + (1 : ℝ) * (CF Γ p).H L998 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L286 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L287 [F17]
  rw [show [F18] ++ L287 ++ [F17] = L1000 from rfl, show [F18] ++ L287 = L997 from rfl,
    show L287 ++ [F17] = L999 from rfl] at hh
  rw [i600 h, i598 h, i599 h, i119 h] at hh
  linarith

theorem row243 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L546 + (1 : ℝ) * (CF Γ p).H L1003 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L666 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L667 [F31]
  rw [show [F22] ++ L667 ++ [F31] = L1005 from rfl, show [F22] ++ L667 = L1002 from rfl,
    show L667 ++ [F31] = L1004 from rfl] at hh
  rw [i603 h, i601 h, i602 h, i358 h] at hh
  linarith

theorem row244 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L841 + (1 : ℝ) * (CF Γ p).H L634 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L241 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L242 [F31]
  rw [show [F22] ++ L242 ++ [F31] = L1007 from rfl, show [F22] ++ L242 = L842 from rfl,
    show L242 ++ [F31] = L732 from rfl] at hh
  rw [i604 h, i480 h, i404 h, i91 h] at hh
  linarith

theorem row245 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L841 + (1 : ℝ) * (CF Γ p).H L1010 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L301 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L301 [F31]
  rw [show [F22] ++ L301 ++ [F31] = L1012 from rfl, show [F22] ++ L301 = L1009 from rfl,
    show L301 ++ [F31] = L1011 from rfl] at hh
  rw [i607 h, i605 h, i606 h] at hh
  linarith

theorem row246 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L596 + (1 : ℝ) * (CF Γ p).H L1015 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L777 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L777 [F43]
  rw [show [F22] ++ L777 ++ [F43] = L1017 from rfl, show [F22] ++ L777 = L1014 from rfl,
    show L777 ++ [F43] = L1016 from rfl] at hh
  rw [i610 h, i608 h, i609 h] at hh
  linarith

theorem row247 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L565 + (1 : ℝ) * (CF Γ p).H L508 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L998 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L1022 [F44]
  rw [show [F29] ++ L1022 ++ [F44] = L1021 from rfl, show [F29] ++ L1022 = L1019 from rfl,
    show L1022 ++ [F44] = L1020 from rfl] at hh
  rw [i613 h, i611 h, i612 h, i614 h] at hh
  linarith

theorem row248 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L565 + (1 : ℝ) * (CF Γ p).H L888 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L886 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L887 [F44]
  rw [show [F29] ++ L887 ++ [F44] = L1025 from rfl, show [F29] ++ L887 = L1023 from rfl,
    show L887 ++ [F44] = L1024 from rfl] at hh
  rw [i617 h, i615 h, i616 h, i512 h] at hh
  linarith

theorem row249 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L581 + (1 : ℝ) * (CF Γ p).H L1026 + (-1 : ℝ) * (CF Γ p).H L880 + (-1 : ℝ) * (CF Γ p).H L580 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L580 [F11]
  rw [show [F22] ++ L580 ++ [F11] = L1028 from rfl, show [F22] ++ L580 = L582 from rfl,
    show L580 ++ [F11] = L1027 from rfl] at hh
  rw [i619 h, i297 h, i618 h] at hh
  linarith

theorem row250 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L584 + (1 : ℝ) * (CF Γ p).H L682 + (-1 : ℝ) * (CF Γ p).H L874 + (-1 : ℝ) * (CF Γ p).H L583 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L583 [F17]
  rw [show [F22] ++ L583 ++ [F17] = L1030 from rfl, show [F22] ++ L583 = L585 from rfl,
    show L583 ++ [F17] = L1029 from rfl] at hh
  rw [i621 h, i298 h, i620 h] at hh
  linarith

theorem row251 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L862 + (1 : ℝ) * (CF Γ p).H L634 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L782 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L1035 [F15]
  rw [show [F22] ++ L1035 ++ [F15] = L1033 from rfl, show [F22] ++ L1035 = L1031 from rfl,
    show L1035 ++ [F15] = L1032 from rfl] at hh
  rw [i624 h, i622 h, i623 h, i625 h] at hh
  linarith

theorem row252 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L612 + (1 : ℝ) * (CF Γ p).H L953 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L1039 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L1040 [F29]
  rw [show [F44] ++ L1040 ++ [F29] = L1038 from rfl, show [F44] ++ L1040 = L1036 from rfl,
    show L1040 ++ [F29] = L1037 from rfl] at hh
  rw [i628 h, i626 h, i627 h, i629 h] at hh
  linarith

theorem row253 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L808 + (1 : ℝ) * (CF Γ p).H L5 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L806 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L1044 [F40]
  rw [show [F44] ++ L1044 ++ [F40] = L1043 from rfl, show [F44] ++ L1044 = L1041 from rfl,
    show L1044 ++ [F40] = L1042 from rfl] at hh
  rw [i632 h, i630 h, i631 h, i633 h] at hh
  linarith

theorem row254 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L975 + (1 : ℝ) * (CF Γ p).H L9 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L1003 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L1047 [F30]
  rw [show [F29] ++ L1047 ++ [F30] = L1046 from rfl, show [F29] ++ L1047 = L1045 from rfl,
    show L1047 ++ [F30] = L10 from rfl] at hh
  rw [i635 h, i634 h, i5 h, i636 h] at hh
  linarith

theorem row255 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L1048 + (1 : ℝ) * (CF Γ p).H L273 + (-1 : ℝ) * (CF Γ p).H L152 + (-1 : ℝ) * (CF Γ p).H L17 = 0 := by
  have hh : (C1 Γ p).H (L1052 ++ L1053 ++ L18) + (C1 Γ p).H L18 = (C1 Γ p).H (L1052 ++ L18) + (C1 Γ p).H (L1053 ++ L18) :=
    Conf.H_copy_ci (src := src0) (V := V0) (hv0 h) (by decide) L1052 L1053 L1052 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1052 ++ L1053 ++ L18 = L1051 from rfl, show L1052 ++ L18 = L1050 from rfl, show L1053 ++ L18 = L1049 from rfl] at hh
  rw [← lift1 h L1051 (by decide) (by decide), ← lift1 h L18 (by decide) (by decide), ← lift1 h L1050 (by decide) (by decide), ← lift1 h L1049 (by decide) (by decide)] at hh
  rw [i639 h, i9 h, i638 h, i637 h] at hh
  linarith

theorem row256 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L127 + (1 : ℝ) * (CF Γ p).H L152 + (-1 : ℝ) * (CF Γ p).H L264 + (-1 : ℝ) * (CF Γ p).H L90 = 0 := by
  have hh : (C2 Γ p).H (L1057 ++ L1058 ++ L91) + (C2 Γ p).H L91 = (C2 Γ p).H (L1057 ++ L91) + (C2 Γ p).H (L1058 ++ L91) :=
    Conf.H_copy_ci (src := src1) (V := V1) (hv1 h) (by decide) L1057 L1058 L1057 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1057 ++ L1058 ++ L91 = L1056 from rfl, show L1057 ++ L91 = L1055 from rfl, show L1058 ++ L91 = L1054 from rfl] at hh
  rw [← lift2 h L1056 (by decide), ← lift2 h L91 (by decide), ← lift2 h L1055 (by decide), ← lift2 h L1054 (by decide)] at hh
  rw [i642 h, i35 h, i641 h, i640 h] at hh
  linarith

theorem row257 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L180 + (1 : ℝ) * (CF Γ p).H L264 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L94 = 0 := by
  have hh : (CF Γ p).H (L1062 ++ L1063 ++ L95) + (CF Γ p).H L95 = (CF Γ p).H (L1062 ++ L95) + (CF Γ p).H (L1063 ++ L95) :=
    Conf.H_copy_ci (src := src2) (V := V2) (hv2 h) (by decide) L1062 L1063 L1057 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L1062 ++ L1063 ++ L95 = L1061 from rfl, show L1062 ++ L95 = L1060 from rfl, show L1063 ++ L95 = L1059 from rfl] at hh
  rw [i645 h, i37 h, i644 h, i643 h] at hh
  linarith

theorem row258 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L297 + (5 : ℝ) * (CF Γ p).H L575 + (-12 : ℝ) * (CF Γ p).H L302 + (6 : ℝ) * (CF Γ p).H L165 + (2 : ℝ) * (CF Γ p).H L299 + (-4 : ℝ) * (CF Γ p).H L210 + (7 : ℝ) * (CF Γ p).H L694 + (2 : ℝ) * (CF Γ p).H L212 + (-3 : ℝ) * (CF Γ p).H L15 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L631 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1064 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1065 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1066 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1067 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1068 from rfl, show ([1] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L211 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1069 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1070 from rfl, show ([2] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L16 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L631, L211, L16, L85, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1071 from rfl] at hL
  rw [i331 h, i646 h, i647 h, i648 h, i649 h, i650 h, i80 h, i651 h, i652 h, i8 h, i653 h] at hL
  linarith

theorem row259 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L68 + (7 : ℝ) * (CF Γ p).H L782 + (-12 : ℝ) * (CF Γ p).H L195 + (5 : ℝ) * (CF Γ p).H L375 + (2 : ℝ) * (CF Γ p).H L663 + (-5 : ℝ) * (CF Γ p).H L176 + (6 : ℝ) * (CF Γ p).H L549 + (2 : ℝ) * (CF Γ p).H L355 + (-1 : ℝ) * (CF Γ p).H L26 := by
  have hL := lem_dfz5 ((CF Γ p).lsp ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L68 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1073 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1074 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1075 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1076 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1077 from rfl, show ([1] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L176 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1078 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1079 from rfl, show ([2] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L26 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L68, L176, L26, L194, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L196 from rfl] at hL
  rw [i654 h, i655 h, i656 h, i657 h, i658 h, i659 h, i660 h, i73 h] at hL
  linarith

theorem row260 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L103 + (9 : ℝ) * (CF Γ p).H L971 + (-14 : ℝ) * (CF Γ p).H L390 + (-3 : ℝ) * (CF Γ p).H L317 + (9 : ℝ) * (CF Γ p).H L383 + (3 : ℝ) * (CF Γ p).H L890 + (-8 : ℝ) * (CF Γ p).H L77 + (13 : ℝ) * (CF Γ p).H L98 + (3 : ℝ) * (CF Γ p).H L896 + (-5 : ℝ) * (CF Γ p).H L19 + (-3 : ℝ) * (CF Γ p).H L116 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L103 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1080 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1081 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1082 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1084 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L891 from rfl, show ([1] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L77 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1085 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1086 from rfl, show ([2] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L19 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L103, L77, L19, L115, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L117 from rfl] at hL
  rw [i661 h, i662 h, i663 h, i664 h, i514 h, i665 h, i666 h, i45 h] at hL
  linarith

theorem row261 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L397 + (5 : ℝ) * (CF Γ p).H L877 + (-12 : ℝ) * (CF Γ p).H L721 + (6 : ℝ) * (CF Γ p).H L352 + (2 : ℝ) * (CF Γ p).H L399 + (-4 : ℝ) * (CF Γ p).H L341 + (7 : ℝ) * (CF Γ p).H L187 + (2 : ℝ) * (CF Γ p).H L260 + (-3 : ℝ) * (CF Γ p).H L72 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1087 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1088 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1089 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1090 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1091 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1092 from rfl, show ([1] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L988 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1093 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1094 from rfl, show ([2] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L73 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1087, L988, L73, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1095 from rfl] at hL
  rw [i667 h, i668 h, i669 h, i670 h, i671 h, i672 h, i590 h, i673 h, i674 h, i28 h, i675 h] at hL
  linarith

theorem row262 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-9 : ℝ) * (CF Γ p).H L341 + (9 : ℝ) * (CF Γ p).H L187 + (-11 : ℝ) * (CF Γ p).H L721 + (-3 : ℝ) * (CF Γ p).H L494 + (11 : ℝ) * (CF Γ p).H L877 + (-4 : ℝ) * (CF Γ p).H L697 + (7 : ℝ) * (CF Γ p).H L527 + (-7 : ℝ) * (CF Γ p).H L72 + (9 : ℝ) * (CF Γ p).H L352 + (3 : ℝ) * (CF Γ p).H L726 + (-2 : ℝ) * (CF Γ p).H L397 + (-3 : ℝ) * (CF Γ p).H L801 := by
  have hL := lem_dfz33 ((CF Γ p).lsp ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L988 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1093 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1097 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1098 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1099 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1100 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1101 from rfl, show ([1] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L73 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1102 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1103 from rfl, show ([2] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1087 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L988, L73, L1087, L164, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1104 from rfl] at hL
  rw [i590 h, i673 h, i676 h, i677 h, i678 h, i679 h, i680 h, i28 h, i681 h, i682 h, i667 h, i683 h] at hL
  linarith

theorem row263 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L246 + (6 : ℝ) * (CF Γ p).H L604 + (-8 : ℝ) * (CF Γ p).H L487 + (-2 : ℝ) * (CF Γ p).H L608 + (5 : ℝ) * (CF Γ p).H L403 + (2 : ℝ) * (CF Γ p).H L537 + (-5 : ℝ) * (CF Γ p).H L177 + (7 : ℝ) * (CF Γ p).H L862 + (2 : ℝ) * (CF Γ p).H L596 + (-2 : ℝ) * (CF Γ p).H L755 + (-2 : ℝ) * (CF Γ p).H L1010 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1105 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1106 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1107 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1108 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1109 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1110 from rfl, show ([1] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L178 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1111 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1112 from rfl, show ([2] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L849 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1105, L178, L849, L54, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1113 from rfl] at hL
  rw [i684 h, i685 h, i686 h, i687 h, i688 h, i689 h, i68 h, i690 h, i691 h, i487 h, i692 h] at hL
  linarith

theorem row264 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L292 + (7 : ℝ) * (CF Γ p).H L464 + (-19 : ℝ) * (CF Γ p).H L270 + (11 : ℝ) * (CF Γ p).H L123 + (3 : ℝ) * (CF Γ p).H L294 + (-5 : ℝ) * (CF Γ p).H L462 + (11 : ℝ) * (CF Γ p).H L694 + (3 : ℝ) * (CF Γ p).H L403 + (-6 : ℝ) * (CF Γ p).H L204 := by
  have hL := lem_dfz56 ((CF Γ p).lsp ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1114 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1115 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1116 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1117 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1118 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1119 from rfl, show ([1] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L463 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1120 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1121 from rfl, show ([2] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L205 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1114, L463, L205, L47, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1122 from rfl] at hL
  rw [i693 h, i694 h, i695 h, i696 h, i697 h, i698 h, i225 h, i699 h, i700 h, i77 h, i701 h] at hL
  linarith

theorem row265 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L273 + (9 : ℝ) * (CF Γ p).H L325 + (-20 : ℝ) * (CF Γ p).H L310 + (9 : ℝ) * (CF Γ p).H L214 + (3 : ℝ) * (CF Γ p).H L152 + (-8 : ℝ) * (CF Γ p).H L339 + (13 : ℝ) * (CF Γ p).H L366 + (3 : ℝ) * (CF Γ p).H L511 + (-5 : ℝ) * (CF Γ p).H L20 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L274 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1124 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1125 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1126 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1127 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1128 from rfl, show ([1] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L340 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1130 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1131 from rfl, show ([2] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L21 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L274, L340, L21, L106, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1132 from rfl] at hL
  rw [i110 h, i702 h, i703 h, i704 h, i705 h, i706 h, i149 h, i707 h, i708 h, i10 h, i709 h] at hL
  linarith

theorem row266 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L394 + (9 : ℝ) * (CF Γ p).H L578 + (-20 : ℝ) * (CF Γ p).H L310 + (9 : ℝ) * (CF Γ p).H L371 + (3 : ℝ) * (CF Γ p).H L366 + (-8 : ℝ) * (CF Γ p).H L42 + (13 : ℝ) * (CF Γ p).H L59 + (3 : ℝ) * (CF Γ p).H L950 + (-5 : ℝ) * (CF Γ p).H L385 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L960 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1135 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1136 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1137 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1138 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1139 from rfl, show ([1] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L43 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1140 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1141 from rfl, show ([2] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1134 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L960, L43, L1134, L157, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1142 from rfl] at hL
  rw [i565 h, i710 h, i711 h, i712 h, i713 h, i714 h, i19 h, i715 h, i716 h, i717 h, i718 h] at hL
  linarith

theorem row267 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L532 + (14 : ℝ) * (CF Γ p).H L407 + (-28 : ℝ) * (CF Γ p).H L502 + (15 : ℝ) * (CF Γ p).H L206 + (4 : ℝ) * (CF Γ p).H L443 + (-13 : ℝ) * (CF Γ p).H L1150 + (23 : ℝ) * (CF Γ p).H L682 + (4 : ℝ) * (CF Γ p).H L990 + (-10 : ℝ) * (CF Γ p).H L172 + (-4 : ℝ) * (CF Γ p).H L1026 := by
  have hL := lem_dfz77 ((CF Γ p).lsp ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L533 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1145 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1146 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1147 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1148 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1149 from rfl, show ([1] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1144 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1151 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1152 from rfl, show ([2] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L749 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L533, L1144, L749, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1153 from rfl] at hL
  rw [i267 h, i719 h, i720 h, i721 h, i722 h, i723 h, i724 h, i725 h, i726 h, i416 h, i727 h] at hL
  linarith

theorem row268 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L392 + (9 : ℝ) * (CF Γ p).H L371 + (-20 : ℝ) * (CF Γ p).H L310 + (9 : ℝ) * (CF Γ p).H L217 + (3 : ℝ) * (CF Γ p).H L325 + (-8 : ℝ) * (CF Γ p).H L383 + (13 : ℝ) * (CF Γ p).H L214 + (3 : ℝ) * (CF Γ p).H L505 + (-5 : ℝ) * (CF Γ p).H L24 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1154 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1156 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1157 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1158 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1159 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1160 from rfl, show ([1] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1155 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1161 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1162 from rfl, show ([2] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L25 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1154, L1155, L25, L133, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1163 from rfl] at hL
  rw [i728 h, i729 h, i730 h, i731 h, i732 h, i733 h, i734 h, i735 h, i736 h, i12 h, i737 h] at hL
  linarith

theorem row269 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L468 + (9 : ℝ) * (CF Γ p).H L448 + (-20 : ℝ) * (CF Γ p).H L264 + (9 : ℝ) * (CF Γ p).H L230 + (3 : ℝ) * (CF Γ p).H L256 + (-8 : ℝ) * (CF Γ p).H L456 + (13 : ℝ) * (CF Γ p).H L55 + (3 : ℝ) * (CF Γ p).H L490 + (-5 : ℝ) * (CF Γ p).H L40 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L548 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1166 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1167 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1168 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1169 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1170 from rfl, show ([1] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1165 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1171 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1172 from rfl, show ([2] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L41 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L548, L1165, L41, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1173 from rfl] at hL
  rw [i278 h, i738 h, i739 h, i740 h, i741 h, i742 h, i743 h, i744 h, i745 h, i18 h, i746 h] at hL
  linarith

theorem row270 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L466 + (9 : ℝ) * (CF Γ p).H L448 + (-20 : ℝ) * (CF Γ p).H L264 + (9 : ℝ) * (CF Γ p).H L227 + (3 : ℝ) * (CF Γ p).H L278 + (-8 : ℝ) * (CF Γ p).H L454 + (13 : ℝ) * (CF Γ p).H L48 + (3 : ℝ) * (CF Γ p).H L484 + (-5 : ℝ) * (CF Γ p).H L37 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1175 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1177 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1178 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1179 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1180 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1181 from rfl, show ([1] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1176 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1182 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1183 from rfl, show ([2] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L38 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1175, L1176, L38, L68, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1184 from rfl] at hL
  rw [i747 h, i748 h, i749 h, i750 h, i751 h, i752 h, i753 h, i754 h, i755 h, i17 h, i756 h] at hL
  linarith

theorem row271 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L208 + (9 : ℝ) * (CF Γ p).H L180 + (-20 : ℝ) * (CF Γ p).H L310 + (9 : ℝ) * (CF Γ p).H L59 + (3 : ℝ) * (CF Γ p).H L217 + (-8 : ℝ) * (CF Γ p).H L369 + (13 : ℝ) * (CF Γ p).H L371 + (3 : ℝ) * (CF Γ p).H L329 + (-5 : ℝ) * (CF Γ p).H L385 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1186 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1190 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1191 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1192 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1193 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1194 from rfl, show ([1] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1187 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1195 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1196 from rfl, show ([2] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1134 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1186, L1187, L1134, L1188, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1197 from rfl] at hL
  rw [i757 h, i758 h, i759 h, i760 h, i761 h, i762 h, i763 h, i764 h, i765 h, i717 h, i766 h] at hL
  linarith

theorem row272 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L559 + (6 : ℝ) * (CF Γ p).H L187 + (-12 : ℝ) * (CF Γ p).H L494 + (5 : ℝ) * (CF Γ p).H L127 + (2 : ℝ) * (CF Γ p).H L220 + (-5 : ℝ) * (CF Γ p).H L341 + (7 : ℝ) * (CF Γ p).H L676 + (2 : ℝ) * (CF Γ p).H L527 + (-2 : ℝ) * (CF Γ p).H L446 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L560 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1200 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1201 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1202 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1203 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1204 from rfl, show ([1] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L988 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1205 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1206 from rfl, show ([2] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1199 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L560, L988, L1199, L159, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1207 from rfl] at hL
  rw [i284 h, i767 h, i768 h, i769 h, i770 h, i771 h, i590 h, i772 h, i773 h, i774 h, i775 h] at hL
  linarith

theorem row273 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L753 + (5 : ℝ) * (CF Γ p).H L604 + (-12 : ℝ) * (CF Γ p).H L608 + (6 : ℝ) * (CF Γ p).H L224 + (2 : ℝ) * (CF Γ p).H L288 + (-4 : ℝ) * (CF Γ p).H L246 + (7 : ℝ) * (CF Γ p).H L248 + (2 : ℝ) * (CF Γ p).H L537 + (-3 : ℝ) * (CF Γ p).H L770 := by
  have hL := lem_dfz7 ((CF Γ p).lsp ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L921 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1209 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1210 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1211 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1212 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1213 from rfl, show ([1] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1105 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1214 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1215 from rfl, show ([2] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L771 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L921, L1105, L771, L641, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1216 from rfl] at hL
  rw [i534 h, i776 h, i777 h, i778 h, i779 h, i780 h, i684 h, i781 h, i782 h, i432 h, i783 h] at hL
  linarith

theorem row274 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-19 : ℝ) * (CF Γ p).H L624 + (18 : ℝ) * (CF Γ p).H L600 + (-27 : ℝ) * (CF Γ p).H L565 + (-6 : ℝ) * (CF Γ p).H L612 + (28 : ℝ) * (CF Γ p).H L426 + (-11 : ℝ) * (CF Γ p).H L975 + (17 : ℝ) * (CF Γ p).H L530 + (-16 : ℝ) * (CF Γ p).H L598 + (25 : ℝ) * (CF Γ p).H L841 + (6 : ℝ) * (CF Γ p).H L1039 + (-9 : ℝ) * (CF Γ p).H L890 + (-6 : ℝ) * (CF Γ p).H L1015 := by
  have hL := lem_dfz35 ((CF Γ p).lsp ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L977 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1219 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1220 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1221 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1222 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1223 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1224 from rfl, show ([1] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L599 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1225 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1226 from rfl, show ([2] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L891 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L977, L599, L891, L1218, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1227 from rfl] at hL
  rw [i580 h, i784 h, i785 h, i786 h, i787 h, i788 h, i789 h, i305 h, i790 h, i791 h, i514 h, i792 h] at hL
  linarith

theorem row275 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L254 + (9 : ℝ) * (CF Γ p).H L1039 + (-14 : ℝ) * (CF Γ p).H L0 + (-3 : ℝ) * (CF Γ p).H L612 + (9 : ℝ) * (CF Γ p).H L862 + (3 : ℝ) * (CF Γ p).H L256 + (-8 : ℝ) * (CF Γ p).H L598 + (13 : ℝ) * (CF Γ p).H L841 + (3 : ℝ) * (CF Γ p).H L600 + (-5 : ℝ) * (CF Γ p).H L385 + (-3 : ℝ) * (CF Γ p).H L982 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1228 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1229 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1230 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1232 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1233 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1234 from rfl, show ([1] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L599 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1235 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L601 from rfl, show ([2] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1134 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1228, L599, L1134, L26, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1236 from rfl] at hL
  rw [i793 h, i794 h, i795 h, i796 h, i797 h, i798 h, i305 h, i799 h, i306 h, i717 h, i800 h] at hL
  linarith

theorem row276 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L103 + (9 : ℝ) * (CF Γ p).H L755 + (-14 : ℝ) * (CF Γ p).H L294 + (-3 : ℝ) * (CF Γ p).H L270 + (9 : ℝ) * (CF Γ p).H L290 + (3 : ℝ) * (CF Γ p).H L204 + (-8 : ℝ) * (CF Γ p).H L47 + (13 : ℝ) * (CF Γ p).H L27 + (3 : ℝ) * (CF Γ p).H L857 + (-5 : ℝ) * (CF Γ p).H L17 + (-3 : ℝ) * (CF Γ p).H L66 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L103 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L849 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1237 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1238 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1240 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1241 from rfl, show ([1] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L47 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1242 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1243 from rfl, show ([2] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L18 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L103, L47, L18, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L67 from rfl] at hL
  rw [i487 h, i801 h, i802 h, i803 h, i804 h, i805 h, i806 h, i9 h, i26 h] at hL
  linarith

theorem row277 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L246 + (9 : ℝ) * (CF Γ p).H L403 + (-14 : ℝ) * (CF Γ p).H L270 + (-3 : ℝ) * (CF Γ p).H L939 + (9 : ℝ) * (CF Γ p).H L236 + (3 : ℝ) * (CF Γ p).H L942 + (-8 : ℝ) * (CF Γ p).H L101 + (13 : ℝ) * (CF Γ p).H L48 + (3 : ℝ) * (CF Γ p).H L431 + (-5 : ℝ) * (CF Γ p).H L454 + (-3 : ℝ) * (CF Γ p).H L719 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1105 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1244 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1245 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1246 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1247 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1248 from rfl, show ([1] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L102 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1249 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1250 from rfl, show ([2] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1176 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1105, L102, L1176, L186, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1251 from rfl] at hL
  rw [i684 h, i807 h, i808 h, i809 h, i810 h, i811 h, i40 h, i812 h, i813 h, i753 h, i814 h] at hL
  linarith

theorem row278 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-5 : ℝ) * (CF Γ p).H L51 + (11 : ℝ) * (CF Γ p).H L37 + (-13 : ℝ) * (CF Γ p).H L48 + (-3 : ℝ) * (CF Γ p).H L473 + (7 : ℝ) * (CF Γ p).H L101 + (3 : ℝ) * (CF Γ p).H L737 + (-9 : ℝ) * (CF Γ p).H L112 + (11 : ℝ) * (CF Γ p).H L27 + (3 : ℝ) * (CF Γ p).H L233 + (-2 : ℝ) * (CF Γ p).H L47 + (-3 : ℝ) * (CF Γ p).H L862 := by
  have hL := lem_dfz60 ((CF Γ p).lsp ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L51 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1252 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1253 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1254 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1255 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1256 from rfl, show ([1] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L112 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1257 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1258 from rfl, show ([2] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L47 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L51, L112, L47, L192, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1259 from rfl] at hL
  rw [i815 h, i816 h, i817 h, i818 h, i819 h, i820 h, i821 h, i822 h] at hL
  linarith

theorem row279 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L466 + (9 : ℝ) * (CF Γ p).H L448 + (-20 : ℝ) * (CF Γ p).H L264 + (9 : ℝ) * (CF Γ p).H L278 + (3 : ℝ) * (CF Γ p).H L227 + (-8 : ℝ) * (CF Γ p).H L456 + (13 : ℝ) * (CF Γ p).H L55 + (3 : ℝ) * (CF Γ p).H L490 + (-5 : ℝ) * (CF Γ p).H L30 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1175 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1260 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1261 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1262 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1263 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1264 from rfl, show ([1] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1165 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1265 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1266 from rfl, show ([2] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L31 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1175, L1165, L31, L51, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1267 from rfl] at hL
  rw [i747 h, i823 h, i824 h, i825 h, i826 h, i827 h, i743 h, i828 h, i829 h, i14 h, i830 h] at hL
  linarith

theorem row280 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-3 : ℝ) * (CF Γ p).H L394 + (6 : ℝ) * (CF Γ p).H L371 + (-12 : ℝ) * (CF Γ p).H L310 + (5 : ℝ) * (CF Γ p).H L366 + (2 : ℝ) * (CF Γ p).H L578 + (-5 : ℝ) * (CF Γ p).H L383 + (7 : ℝ) * (CF Γ p).H L214 + (2 : ℝ) * (CF Γ p).H L505 + (-2 : ℝ) * (CF Γ p).H L20 := by
  have hL := lem_dfz8 ((CF Γ p).lsp ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L960 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1269 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1270 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1271 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1272 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1273 from rfl, show ([1] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1155 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1274 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1275 from rfl, show ([2] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L21 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L960, L1155, L21, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1276 from rfl] at hL
  rw [i565 h, i831 h, i832 h, i833 h, i834 h, i835 h, i734 h, i836 h, i837 h, i10 h, i838 h] at hL
  linarith

theorem row281 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L13 + (9 : ℝ) * (CF Γ p).H L45 + (-17 : ℝ) * (CF Γ p).H L950 + (9 : ℝ) * (CF Γ p).H L24 + (3 : ℝ) * (CF Γ p).H L42 + (-8 : ℝ) * (CF Γ p).H L179 + (13 : ℝ) * (CF Γ p).H L156 + (3 : ℝ) * (CF Γ p).H L955 + (-5 : ℝ) * (CF Γ p).H L155 + (-3 : ℝ) * (CF Γ p).H L750 := by
  have hL := lem_dfz109 ((CF Γ p).lsp ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L14 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L776 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1278 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1279 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1280 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1281 from rfl, show ([1] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L179 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1282 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1283 from rfl, show ([2] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L155 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L14, L179, L155, L62, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1284 from rfl] at hL
  rw [i7 h, i435 h, i839 h, i840 h, i841 h, i842 h, i843 h, i844 h, i845 h] at hL
  linarith

theorem row282 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-4 : ℝ) * (CF Γ p).H L103 + (7 : ℝ) * (CF Γ p).H L755 + (-8 : ℝ) * (CF Γ p).H L270 + (-2 : ℝ) * (CF Γ p).H L294 + (5 : ℝ) * (CF Γ p).H L204 + (2 : ℝ) * (CF Γ p).H L290 + (-5 : ℝ) * (CF Γ p).H L176 + (6 : ℝ) * (CF Γ p).H L770 + (2 : ℝ) * (CF Γ p).H L549 + (-1 : ℝ) * (CF Γ p).H L11 + (-2 : ℝ) * (CF Γ p).H L15 := by
  have hL := lem_dfz5 ((CF Γ p).lsp ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L103 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1285 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1286 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1288 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1289 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1290 from rfl, show ([1] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L176 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1291 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1292 from rfl, show ([2] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L12 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L103, L176, L12, L14, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L16 from rfl] at hL
  rw [i846 h, i847 h, i848 h, i849 h, i850 h, i851 h, i852 h, i6 h, i8 h] at hL
  linarith

theorem row283 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-12 : ℝ) * (CF Γ p).H L647 + (14 : ℝ) * (CF Γ p).H L452 + (-38 : ℝ) * (CF Γ p).H L481 + (21 : ℝ) * (CF Γ p).H L212 + (11 : ℝ) * (CF Γ p).H L563 + (-13 : ℝ) * (CF Γ p).H L450 + (22 : ℝ) * (CF Γ p).H L443 + (4 : ℝ) * (CF Γ p).H L774 + (-9 : ℝ) * (CF Γ p).H L532 := by
  have hL := lem_dfz107 ((CF Γ p).lsp ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2, 3] (by decide) ({0, 2, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1293 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1294 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1295 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1296 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1297 from rfl, show ([0, 2, 3] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1298 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1299 from rfl, show ([1] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L993 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1300 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1301 from rfl, show ([2] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L533 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L1293, L993, L533, L223, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1302 from rfl] at hL
  rw [i853 h, i854 h, i855 h, i856 h, i857 h, i858 h, i859 h, i594 h, i860 h, i861 h, i267 h, i862 h] at hL
  linarith

theorem row284 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-12 : ℝ) * (CF Γ p).H L624 + (78 : ℝ) * (CF Γ p).H L600 + (-144 : ℝ) * (CF Γ p).H L565 + (-22 : ℝ) * (CF Γ p).H L0 + (78 : ℝ) * (CF Γ p).H L426 + (11 : ℝ) * (CF Γ p).H L473 + (-77 : ℝ) * (CF Γ p).H L341 + (143 : ℝ) * (CF Γ p).H L187 + (11 : ℝ) * (CF Γ p).H L508 + (-66 : ℝ) * (CF Γ p).H L420 := by
  have hL := lem_matus11 ((CF Γ p).lsp ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L977 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1305 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1306 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1307 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1308 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1309 from rfl, show ([1] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L988 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1310 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1311 from rfl, show ([2] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L428 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L977, L988, L428, L1304, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1312 from rfl] at hL
  rw [i580 h, i863 h, i864 h, i865 h, i866 h, i867 h, i590 h, i868 h, i869 h, i203 h, i870 h] at hL
  linarith

theorem row285 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-8 : ℝ) * (CF Γ p).H L11 + (36 : ℝ) * (CF Γ p).H L762 + (-71 : ℝ) * (CF Γ p).H L202 + (36 : ℝ) * (CF Γ p).H L198 + (7 : ℝ) * (CF Γ p).H L200 + (-35 : ℝ) * (CF Γ p).H L82 + (63 : ℝ) * (CF Γ p).H L98 + (7 : ℝ) * (CF Γ p).H L139 + (-28 : ℝ) * (CF Γ p).H L29 + (-7 : ℝ) * (CF Γ p).H L409 := by
  have hL := lem_matus7 ((CF Γ p).lsp ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L12 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1314 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1315 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1316 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1317 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1318 from rfl, show ([1] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L82 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L435 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1319 from rfl, show ([2] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L29 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L183, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1320 from rfl] at hL
  rw [i6 h, i871 h, i872 h, i873 h, i874 h, i875 h, i207 h, i876 h, i877 h] at hL
  linarith

theorem row286 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-8 : ℝ) * (CF Γ p).H L11 + (36 : ℝ) * (CF Γ p).H L762 + (-64 : ℝ) * (CF Γ p).H L202 + (-7 : ℝ) * (CF Γ p).H L990 + (36 : ℝ) * (CF Γ p).H L198 + (7 : ℝ) * (CF Γ p).H L204 + (-35 : ℝ) * (CF Γ p).H L82 + (63 : ℝ) * (CF Γ p).H L98 + (7 : ℝ) * (CF Γ p).H L1150 + (-28 : ℝ) * (CF Γ p).H L29 + (-7 : ℝ) * (CF Γ p).H L172 := by
  have hL := lem_matus7 ((CF Γ p).lsp ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L12 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1314 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1315 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1321 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1317 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1322 from rfl, show ([1] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L82 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L435 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1323 from rfl, show ([2] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L29 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L12, L82, L29, L65, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L173 from rfl] at hL
  rw [i6 h, i871 h, i872 h, i878 h, i874 h, i879 h, i207 h, i880 h, i66 h] at hL
  linarith

theorem row287 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-18 : ℝ) * (CF Γ p).H L753 + (171 : ℝ) * (CF Γ p).H L604 + (-324 : ℝ) * (CF Γ p).H L487 + (-17 : ℝ) * (CF Γ p).H L608 + (171 : ℝ) * (CF Γ p).H L757 + (17 : ℝ) * (CF Γ p).H L224 + (-170 : ℝ) * (CF Γ p).H L394 + (323 : ℝ) * (CF Γ p).H L371 + (17 : ℝ) * (CF Γ p).H L366 + (-153 : ℝ) * (CF Γ p).H L519 + (-17 : ℝ) * (CF Γ p).H L310 := by
  have hL := lem_matus17 ((CF Γ p).lsp ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L921 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1325 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1326 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1327 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1328 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1329 from rfl, show ([1] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L960 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1330 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1331 from rfl, show ([2] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1324 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L921, L960, L1324, L89, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1332 from rfl] at hL
  rw [i534 h, i881 h, i882 h, i883 h, i884 h, i885 h, i565 h, i886 h, i887 h, i888 h, i889 h] at hL
  linarith

theorem row288 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-11 : ℝ) * (CF Γ p).H L433 + (66 : ℝ) * (CF Γ p).H L870 + (-141 : ℝ) * (CF Γ p).H L502 + (66 : ℝ) * (CF Γ p).H L407 + (10 : ℝ) * (CF Γ p).H L390 + (-65 : ℝ) * (CF Γ p).H L762 + (120 : ℝ) * (CF Γ p).H L202 + (10 : ℝ) * (CF Γ p).H L990 + (-55 : ℝ) * (CF Γ p).H L139 := by
  have hL := lem_matus10 ((CF Γ p).lsp ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L434 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1335 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1336 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1337 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1338 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1339 from rfl, show ([1] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L763 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1340 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1341 from rfl, show ([2] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1334 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L434, L763, L1334, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1342 from rfl] at hL
  rw [i206 h, i890 h, i891 h, i892 h, i893 h, i894 h, i425 h, i895 h, i896 h, i897 h, i898 h] at hL
  linarith

theorem row289 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-16 : ℝ) * (CF Γ p).H L388 + (136 : ℝ) * (CF Γ p).H L390 + (-256 : ℝ) * (CF Γ p).H L502 + (-15 : ℝ) * (CF Γ p).H L487 + (136 : ℝ) * (CF Γ p).H L206 + (15 : ℝ) * (CF Γ p).H L757 + (-135 : ℝ) * (CF Γ p).H L441 + (255 : ℝ) * (CF Γ p).H L443 + (15 : ℝ) * (CF Γ p).H L784 + (-120 : ℝ) * (CF Γ p).H L532 + (-15 : ℝ) * (CF Γ p).H L481 := by
  have hL := lem_matus15 ((CF Γ p).lsp ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L388 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1344 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1345 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1346 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1347 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1348 from rfl, show ([1] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L441 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1349 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1350 from rfl, show ([2] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L533 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L388, L441, L533, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1351 from rfl] at hL
  rw [i899 h, i900 h, i901 h, i902 h, i903 h, i904 h, i905 h, i267 h, i906 h] at hL
  linarith

theorem row290 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-63 : ℝ) * (CF Γ p).H L158 + (2016 : ℝ) * (CF Γ p).H L700 + (-4093 : ℝ) * (CF Γ p).H L270 + (2016 : ℝ) * (CF Γ p).H L337 + (62 : ℝ) * (CF Γ p).H L220 + (-2015 : ℝ) * (CF Γ p).H L569 + (3968 : ℝ) * (CF Γ p).H L694 + (62 : ℝ) * (CF Γ p).H L711 + (-1953 : ℝ) * (CF Γ p).H L66 := by
  have hL := lem_matus62 ((CF Γ p).lsp ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L159 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1354 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1355 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1356 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1357 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1358 from rfl, show ([1] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L570 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1359 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1360 from rfl, show ([2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1353 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1361 from rfl] at hL
  rw [i60 h, i907 h, i908 h, i909 h, i910 h, i911 h, i290 h, i912 h, i913 h, i914 h, i915 h] at hL
  linarith

theorem row291 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-58 : ℝ) * (CF Γ p).H L158 + (1711 : ℝ) * (CF Γ p).H L700 + (-3478 : ℝ) * (CF Γ p).H L270 + (1711 : ℝ) * (CF Γ p).H L337 + (57 : ℝ) * (CF Γ p).H L220 + (-1710 : ℝ) * (CF Γ p).H L569 + (3363 : ℝ) * (CF Γ p).H L694 + (57 : ℝ) * (CF Γ p).H L711 + (-1653 : ℝ) * (CF Γ p).H L66 := by
  have hL := lem_matus57 ((CF Γ p).lsp ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L159 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1354 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1355 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1356 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1357 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1358 from rfl, show ([1] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L570 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1359 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1360 from rfl, show ([2] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1353 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L159, L570, L1353, L176, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1361 from rfl] at hL
  rw [i60 h, i907 h, i908 h, i909 h, i910 h, i911 h, i290 h, i912 h, i913 h, i914 h, i915 h] at hL
  linarith

theorem row292 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (-17 : ℝ) * (CF Γ p).H L341 + (153 : ℝ) * (CF Γ p).H L600 + (-289 : ℝ) * (CF Γ p).H L612 + (-16 : ℝ) * (CF Γ p).H L565 + (153 : ℝ) * (CF Γ p).H L527 + (16 : ℝ) * (CF Γ p).H L998 + (-152 : ℝ) * (CF Γ p).H L394 + (288 : ℝ) * (CF Γ p).H L366 + (16 : ℝ) * (CF Γ p).H L371 + (-136 : ℝ) * (CF Γ p).H L517 + (-16 : ℝ) * (CF Γ p).H L310 := by
  have hL := lem_matus16 ((CF Γ p).lsp ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))]) (Conf.valid_lsp (hvF h) ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))])
  rw [Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0] (by decide) ({0} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1] (by decide) ({0, 1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 2] (by decide) ({0, 1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 1, 3] (by decide) ({0, 1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 2] (by decide) ({0, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [0, 3] (by decide) ({0, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1] (by decide) ({1} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 2] (by decide) ({1, 2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [1, 3] (by decide) ({1, 3} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2] (by decide) ({2} : Finset (Fin 9)) (by decide), Conf.H_lsp (hvF h).nonneg ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] [2, 3] (by decide) ({2, 3} : Finset (Fin 9)) (by decide)] at hL
  rw [show ([0] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L988 from rfl, show ([0, 1] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1363 from rfl, show ([0, 1, 2] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1364 from rfl, show ([0, 1, 3] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1365 from rfl, show ([0, 2] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1366 from rfl, show ([0, 3] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1367 from rfl, show ([1] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L960 from rfl, show ([1, 2] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1368 from rfl, show ([1, 3] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1369 from rfl, show ([2] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L610 from rfl, show ([2, 3] : List (Fin 9)).flatMap ![L988, L960, L610, L103, ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6)), ([] : List (Form 6))] = L1370 from rfl] at hL
  rw [i590 h, i916 h, i917 h, i918 h, i919 h, i920 h, i565 h, i921 h, i922 h, i313 h, i923 h] at hL
  linarith

theorem row293 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L88 + (-1 : ℝ) * (CF Γ p).H L22 = 0 := by
  have hh : (C1 Γ p).H (L89 ++ ([] : List (Form 6))) = (C1 Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L89 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L89 ++ ([] : List (Form 6)) = L89 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  rw [← lift1 h L23 (by decide) (by decide), ← lift1 h L89 (by decide) (by decide)] at hh
  rw [i11 h, i34 h] at hh
  linarith

theorem row294 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L39 + (-1 : ℝ) * (CF Γ p).H L35 = 0 := by
  have hh : (C1 Γ p).H (L39 ++ ([] : List (Form 6))) = (C1 Γ p).H (L36 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L39 ([] : List (Form 6)) L36 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L39 ++ ([] : List (Form 6)) = L39 from rfl, show L36 ++ ([] : List (Form 6)) = L36 from rfl] at hh
  rw [← lift1 h L36 (by decide) (by decide), ← lift1 h L39 (by decide) (by decide)] at hh
  rw [i16 h] at hh
  linarith

theorem row295 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L1048 + (-1 : ℝ) * (CF Γ p).H L273 = 0 := by
  have hh : (C1 Γ p).H (L1372 ++ ([] : List (Form 6))) = (C1 Γ p).H (L274 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L1372 ([] : List (Form 6)) L274 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1372 ++ ([] : List (Form 6)) = L1372 from rfl, show L274 ++ ([] : List (Form 6)) = L274 from rfl] at hh
  rw [← lift1 h L274 (by decide) (by decide), ← lift1 h L1372 (by decide) (by decide)] at hh
  rw [i110 h, i924 h] at hh
  linarith

theorem row296 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L11 + (-1 : ℝ) * (CF Γ p).H L17 = 0 := by
  have hh : (C2 Γ p).H (L12 ++ ([] : List (Form 6))) = (C2 Γ p).H (L18 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L12 ([] : List (Form 6)) L18 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L12 ++ ([] : List (Form 6)) = L12 from rfl, show L18 ++ ([] : List (Form 6)) = L18 from rfl] at hh
  rw [← lift2 h L18 (by decide), ← lift2 h L12 (by decide)] at hh
  rw [i9 h, i6 h] at hh
  linarith

theorem row297 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L26 + (-1 : ℝ) * (CF Γ p).H L35 = 0 := by
  have hh : (C2 Γ p).H (L26 ++ ([] : List (Form 6))) = (C2 Γ p).H (L36 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L26 ([] : List (Form 6)) L36 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L26 ++ ([] : List (Form 6)) = L26 from rfl, show L36 ++ ([] : List (Form 6)) = L36 from rfl] at hh
  rw [← lift2 h L36 (by decide), ← lift2 h L26 (by decide)] at hh
  rw [i16 h] at hh
  linarith

theorem row298 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L559 + (-1 : ℝ) * (CF Γ p).H L273 = 0 := by
  have hh : (C2 Γ p).H (L560 ++ ([] : List (Form 6))) = (C2 Γ p).H (L274 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L560 ([] : List (Form 6)) L274 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L560 ++ ([] : List (Form 6)) = L560 from rfl, show L274 ++ ([] : List (Form 6)) = L274 from rfl] at hh
  rw [← lift2 h L274 (by decide), ← lift2 h L560 (by decide)] at hh
  rw [i110 h, i284 h] at hh
  linarith

theorem row299 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L29 + (-1 : ℝ) * (CF Γ p).H L39 = 0 := by
  have hh : (C2 Γ p).H (L29 ++ ([] : List (Form 6))) = (C2 Γ p).H (L39 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L29 ([] : List (Form 6)) L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L29 ++ ([] : List (Form 6)) = L29 from rfl, show L39 ++ ([] : List (Form 6)) = L39 from rfl] at hh
  rw [← lift2 h L39 (by decide), ← lift2 h L29 (by decide)] at hh
  linarith

end EntropyBounds.GlueG.Certs.CL3B6SC
