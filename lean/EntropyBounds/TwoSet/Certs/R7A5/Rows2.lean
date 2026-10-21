import EntropyBounds.TwoSet.Certs.R7A5.Ids0
import EntropyBounds.TwoSet.Certs.R7A5.Ids1
import EntropyBounds.TwoSet.Certs.R7A5.Ids2
import EntropyBounds.TwoSet.Certs.R7A5.Ids3
import EntropyBounds.TwoSet.Certs.R7A5.Ids4
import EntropyBounds.TwoSet.Certs.R7A5.Ids5
import EntropyBounds.TwoSet.Certs.R7A5.Ids6
import EntropyBounds.TwoSet.Certs.R7A5.Ids7
import EntropyBounds.TwoSet.Certs.R7A5.Ids8
import EntropyBounds.TwoSet.Certs.R7A5.Ids9
import EntropyBounds.TwoSet.Certs.R7A5.Ids10
import EntropyBounds.TwoSet.Certs.R7A5.Ids11
import EntropyBounds.TwoSet.Certs.R7A5.Ids12
import EntropyBounds.TwoSet.Certs.R7A5.Ids13
import EntropyBounds.TwoSet.Certs.R7A5.Ids14
import EntropyBounds.TwoSet.Certs.R7A5.Ids15
import EntropyBounds.TwoSet.Certs.R7A5.Ids16
import EntropyBounds.TwoSet.Certs.R7A5.Ids17
import EntropyBounds.TwoSet.Certs.R7A5.Ids18
import EntropyBounds.TwoSet.Certs.R7A5.Ids19
import EntropyBounds.TwoSet.Certs.R7A5.Ids20
import EntropyBounds.TwoSet.Certs.R7A5.Ids21
import EntropyBounds.TwoSet.Certs.R7A5.Ids22
import EntropyBounds.TwoSet.Certs.R7A5.Ids23
import EntropyBounds.TwoSet.Certs.R7A5.Ids24
import EntropyBounds.TwoSet.Certs.R7A5.Ids25
import EntropyBounds.TwoSet.Certs.R7A5.Ids26
import EntropyBounds.TwoSet.Certs.R7A5.Ids27
import EntropyBounds.TwoSet.Certs.R7A5.Ids28
import EntropyBounds.TwoSet.Certs.R7A5.Ids29
import EntropyBounds.TwoSet.Certs.R7A5.Ids30
import EntropyBounds.TwoSet.Certs.R7A5.Ids31
import EntropyBounds.TwoSet.Certs.R7A5.Ids32
import EntropyBounds.TwoSet.Certs.R7A5.Ids33
import EntropyBounds.TwoSet.Certs.R7A5.Ids34
import EntropyBounds.TwoSet.Certs.R7A5.Ids35
import EntropyBounds.TwoSet.Certs.R7A5.Ids36
import EntropyBounds.TwoSet.Certs.R7A5.Ids37
import EntropyBounds.TwoSet.Certs.R7A5.Ids38
import EntropyBounds.TwoSet.Certs.R7A5.Ids39
import EntropyBounds.TwoSet.Certs.R7A5.Ids40
import EntropyBounds.TwoSet.Certs.R7A5.Ids41
import EntropyBounds.TwoSet.Certs.R7A5.Ids42
import EntropyBounds.TwoSet.Certs.R7A5.Ids43
import EntropyBounds.TwoSet.Certs.R7A5.Ids44
import EntropyBounds.TwoSet.Certs.R7A5.Ids45
import EntropyBounds.TwoSet.Certs.R7A5.Ids46
import EntropyBounds.TwoSet.Certs.R7A5.Ids47
import EntropyBounds.Iid.NonShannon
import EntropyBounds.TwoSet.Common
import EntropyBounds.TwoSet.Mirror

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset Pointwise

namespace EntropyBounds.TwoSet.Certs.R7A5

open SumsDifferences SumsDifferences.NonShannon EntropyBounds.Iid EntropyBounds.TwoSet SumsDifferences.CoupledForms

theorem row300 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L820 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L815 := by
  have h := HLm_submod hΓ [F0] L1560 [F3]
  rw [show [F0] ++ L1560 ++ [F3] = L1559 from rfl, show [F0] ++ L1560 = L1557 from rfl,
    show L1560 ++ [F3] = L1558 from rfl] at h
  rw [i797 hinj, i795 hinj, i796 hinj, i798 hinj] at h
  linarith

theorem row301 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L609 + (1 : ℝ) * HLm Γ 5 L1562 + (-1 : ℝ) * HLm Γ 5 L1564 + (-1 : ℝ) * HLm Γ 5 L1566 := by
  have h := HLm_submod hΓ [F0] L1566 [F2]
  rw [show [F0] ++ L1566 ++ [F2] = L1565 from rfl, show [F0] ++ L1566 = L1561 from rfl,
    show L1566 ++ [F2] = L1563 from rfl] at h
  rw [i801 hinj, i799 hinj, i800 hinj] at h
  linarith

theorem row302 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1567 + (1 : ℝ) * HLm Γ 5 L1569 + (-1 : ℝ) * HLm Γ 5 L1571 + (-1 : ℝ) * HLm Γ 5 L1573 := by
  have h := HLm_submod hΓ [F3] L1574 [F67]
  rw [show [F3] ++ L1574 ++ [F67] = L1572 from rfl, show [F3] ++ L1574 = L1568 from rfl,
    show L1574 ++ [F67] = L1570 from rfl] at h
  rw [i804 hinj, i802 hinj, i803 hinj, i805 hinj] at h
  linarith

theorem row303 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L669 + (1 : ℝ) * HLm Γ 5 L1576 + (-1 : ℝ) * HLm Γ 5 L1406 + (-1 : ℝ) * HLm Γ 5 L1579 := by
  have h := HLm_submod hΓ [F0] L1580 [F1]
  rw [show [F0] ++ L1580 ++ [F1] = L1578 from rfl, show [F0] ++ L1580 = L1575 from rfl,
    show L1580 ++ [F1] = L1577 from rfl] at h
  rw [i808 hinj, i806 hinj, i807 hinj, i809 hinj] at h
  linarith

theorem row304 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1581 + (1 : ℝ) * HLm Γ 5 L1583 + (-1 : ℝ) * HLm Γ 5 L1585 + (-1 : ℝ) * HLm Γ 5 L1587 := by
  have h := HLm_submod hΓ [F0] L1588 [F43]
  rw [show [F0] ++ L1588 ++ [F43] = L1586 from rfl, show [F0] ++ L1588 = L1582 from rfl,
    show L1588 ++ [F43] = L1584 from rfl] at h
  rw [i812 hinj, i810 hinj, i811 hinj, i813 hinj] at h
  linarith

theorem row305 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L831 + (1 : ℝ) * HLm Γ 5 L1590 + (-1 : ℝ) * HLm Γ 5 L1592 + (-1 : ℝ) * HLm Γ 5 L1594 := by
  have h := HLm_submod hΓ [F0] L1595 [F1]
  rw [show [F0] ++ L1595 ++ [F1] = L1593 from rfl, show [F0] ++ L1595 = L1589 from rfl,
    show L1595 ++ [F1] = L1591 from rfl] at h
  rw [i816 hinj, i814 hinj, i815 hinj, i817 hinj] at h
  linarith

theorem row306 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L772 + (1 : ℝ) * HLm Γ 5 L799 + (-1 : ℝ) * HLm Γ 5 L1597 + (-1 : ℝ) * HLm Γ 5 L274 := by
  have h := HLm_submod hΓ [F12] L275 [F16]
  rw [show [F12] ++ L275 ++ [F16] = L1598 from rfl, show [F12] ++ L275 = L773 from rfl,
    show L275 ++ [F16] = L1596 from rfl] at h
  rw [i819 hinj, i343 hinj, i818 hinj, i103 hinj] at h
  linarith

theorem row307 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L778 + (1 : ℝ) * HLm Γ 5 L794 + (-1 : ℝ) * HLm Γ 5 L1601 + (-1 : ℝ) * HLm Γ 5 L792 := by
  have h := HLm_submod hΓ [F1] L1603 [F67]
  rw [show [F1] ++ L1603 ++ [F67] = L1602 from rfl, show [F1] ++ L1603 = L1599 from rfl,
    show L1603 ++ [F67] = L1600 from rfl] at h
  rw [i822 hinj, i820 hinj, i821 hinj, i823 hinj] at h
  linarith

theorem row308 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1604 + (1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L1608 + (-1 : ℝ) * HLm Γ 5 L1610 := by
  have h := HLm_submod hΓ [F2] L1611 [F16]
  rw [show [F2] ++ L1611 ++ [F16] = L1609 from rfl, show [F2] ++ L1611 = L1605 from rfl,
    show L1611 ++ [F16] = L1607 from rfl] at h
  rw [i826 hinj, i824 hinj, i825 hinj, i827 hinj] at h
  linarith

theorem row309 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L638 + (1 : ℝ) * HLm Γ 5 L784 + (-1 : ℝ) * HLm Γ 5 L1614 + (-1 : ℝ) * HLm Γ 5 L782 := by
  have h := HLm_submod hΓ [F0] L783 [F67]
  rw [show [F0] ++ L783 ++ [F67] = L1615 from rfl, show [F0] ++ L783 = L1612 from rfl,
    show L783 ++ [F67] = L1613 from rfl] at h
  rw [i830 hinj, i828 hinj, i829 hinj, i349 hinj] at h
  linarith

theorem row310 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1616 + (1 : ℝ) * HLm Γ 5 L1618 + (-1 : ℝ) * HLm Γ 5 L1537 + (-1 : ℝ) * HLm Γ 5 L786 := by
  have h := HLm_submod hΓ [F1] L1621 [F52]
  rw [show [F1] ++ L1621 ++ [F52] = L1620 from rfl, show [F1] ++ L1621 = L1617 from rfl,
    show L1621 ++ [F52] = L1619 from rfl] at h
  rw [i833 hinj, i831 hinj, i832 hinj, i834 hinj] at h
  linarith

theorem row311 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1622 + (1 : ℝ) * HLm Γ 5 L1624 + (-1 : ℝ) * HLm Γ 5 L1626 + (-1 : ℝ) * HLm Γ 5 L1628 := by
  have h := HLm_submod hΓ [F0] L1629 [F5]
  rw [show [F0] ++ L1629 ++ [F5] = L1627 from rfl, show [F0] ++ L1629 = L1623 from rfl,
    show L1629 ++ [F5] = L1625 from rfl] at h
  rw [i837 hinj, i835 hinj, i836 hinj, i838 hinj] at h
  linarith

theorem row312 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1630 + (1 : ℝ) * HLm Γ 5 L1632 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1635 := by
  have h := HLm_submod hΓ [F0] L1636 [F5]
  rw [show [F0] ++ L1636 ++ [F5] = L1634 from rfl, show [F0] ++ L1636 = L1631 from rfl,
    show L1636 ++ [F5] = L1633 from rfl] at h
  rw [i841 hinj, i839 hinj, i840 hinj, i842 hinj] at h
  linarith

theorem row313 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1637 + (1 : ℝ) * HLm Γ 5 L1639 + (-1 : ℝ) * HLm Γ 5 L1641 + (-1 : ℝ) * HLm Γ 5 L1643 := by
  have h := HLm_submod hΓ [F0] L1644 [F2]
  rw [show [F0] ++ L1644 ++ [F2] = L1642 from rfl, show [F0] ++ L1644 = L1638 from rfl,
    show L1644 ++ [F2] = L1640 from rfl] at h
  rw [i845 hinj, i843 hinj, i844 hinj, i846 hinj] at h
  linarith

theorem row314 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1645 + (1 : ℝ) * HLm Γ 5 L908 + (-1 : ℝ) * HLm Γ 5 L1648 + (-1 : ℝ) * HLm Γ 5 L868 := by
  have h := HLm_submod hΓ [F47] L869 [F9]
  rw [show [F47] ++ L869 ++ [F9] = L1649 from rfl, show [F47] ++ L869 = L1646 from rfl,
    show L869 ++ [F9] = L1647 from rfl] at h
  rw [i849 hinj, i847 hinj, i848 hinj, i395 hinj] at h
  linarith

theorem row315 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1650 + (1 : ℝ) * HLm Γ 5 L1652 + (-1 : ℝ) * HLm Γ 5 L1654 + (-1 : ℝ) * HLm Γ 5 L1656 := by
  have h := HLm_submod hΓ [F107] L1657 [F67]
  rw [show [F107] ++ L1657 ++ [F67] = L1655 from rfl, show [F107] ++ L1657 = L1651 from rfl,
    show L1657 ++ [F67] = L1653 from rfl] at h
  rw [i852 hinj, i850 hinj, i851 hinj, i853 hinj] at h
  linarith

theorem row316 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L887 + (1 : ℝ) * HLm Γ 5 L1659 + (-1 : ℝ) * HLm Γ 5 L1661 + (-1 : ℝ) * HLm Γ 5 L885 := by
  have h := HLm_submod hΓ [F67] L1663 [F36]
  rw [show [F67] ++ L1663 ++ [F36] = L1662 from rfl, show [F67] ++ L1663 = L1658 from rfl,
    show L1663 ++ [F36] = L1660 from rfl] at h
  rw [i856 hinj, i854 hinj, i855 hinj, i857 hinj] at h
  linarith

theorem row317 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L881 + (1 : ℝ) * HLm Γ 5 L1664 + (-1 : ℝ) * HLm Γ 5 L1666 + (-1 : ℝ) * HLm Γ 5 L879 := by
  have h := HLm_submod hΓ [F1] L880 [F7]
  rw [show [F1] ++ L880 ++ [F7] = L1667 from rfl, show [F1] ++ L880 = L882 from rfl,
    show L880 ++ [F7] = L1665 from rfl] at h
  rw [i859 hinj, i401 hinj, i858 hinj, i400 hinj] at h
  linarith

theorem row318 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1668 + (1 : ℝ) * HLm Γ 5 L1670 + (-1 : ℝ) * HLm Γ 5 L1672 + (-1 : ℝ) * HLm Γ 5 L1674 := by
  have h := HLm_submod hΓ [F2] L1675 [F33]
  rw [show [F2] ++ L1675 ++ [F33] = L1673 from rfl, show [F2] ++ L1675 = L1669 from rfl,
    show L1675 ++ [F33] = L1671 from rfl] at h
  rw [i862 hinj, i860 hinj, i861 hinj, i863 hinj] at h
  linarith

theorem row319 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L989 + (1 : ℝ) * HLm Γ 5 L1677 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L920 := by
  have h := HLm_submod hΓ [F0] L921 [F108]
  rw [show [F0] ++ L921 ++ [F108] = L1679 from rfl, show [F0] ++ L921 = L1676 from rfl,
    show L921 ++ [F108] = L1678 from rfl] at h
  rw [i866 hinj, i864 hinj, i865 hinj, i423 hinj] at h
  linarith

theorem row320 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1680 + (1 : ℝ) * HLm Γ 5 L1198 + (-1 : ℝ) * HLm Γ 5 L1683 + (-1 : ℝ) * HLm Γ 5 L914 := by
  have h := HLm_submod hΓ [F0] L915 [F62]
  rw [show [F0] ++ L915 ++ [F62] = L1684 from rfl, show [F0] ++ L915 = L1681 from rfl,
    show L915 ++ [F62] = L1682 from rfl] at h
  rw [i869 hinj, i867 hinj, i868 hinj, i420 hinj] at h
  linarith

theorem row321 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L722 + (1 : ℝ) * HLm Γ 5 L1686 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L914 := by
  have h := HLm_submod hΓ [F51] L915 [F9]
  rw [show [F51] ++ L915 ++ [F9] = L1688 from rfl, show [F51] ++ L915 = L1685 from rfl,
    show L915 ++ [F9] = L1687 from rfl] at h
  rw [i872 hinj, i870 hinj, i871 hinj, i420 hinj] at h
  linarith

theorem row322 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L928 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L926 := by
  have h := HLm_submod hΓ [F10] L927 [F67]
  rw [show [F10] ++ L927 ++ [F67] = L1691 from rfl, show [F10] ++ L927 = L1689 from rfl,
    show L927 ++ [F67] = L1690 from rfl] at h
  rw [i875 hinj, i873 hinj, i874 hinj, i426 hinj] at h
  linarith

theorem row323 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L553 + (1 : ℝ) * HLm Γ 5 L1119 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L1696 := by
  have h := HLm_submod hΓ [F0] L1697 [F2]
  rw [show [F0] ++ L1697 ++ [F2] = L1695 from rfl, show [F0] ++ L1697 = L1692 from rfl,
    show L1697 ++ [F2] = L1693 from rfl] at h
  rw [i878 hinj, i876 hinj, i877 hinj, i879 hinj] at h
  linarith

theorem row324 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1698 + (1 : ℝ) * HLm Γ 5 L963 + (-1 : ℝ) * HLm Γ 5 L1701 + (-1 : ℝ) * HLm Γ 5 L1703 := by
  have h := HLm_submod hΓ [F7] L1704 [F2]
  rw [show [F7] ++ L1704 ++ [F2] = L1702 from rfl, show [F7] ++ L1704 = L1699 from rfl,
    show L1704 ++ [F2] = L1700 from rfl] at h
  rw [i882 hinj, i880 hinj, i881 hinj, i883 hinj] at h
  linarith

theorem row325 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L970 + (1 : ℝ) * HLm Γ 5 L1706 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L968 := by
  have h := HLm_submod hΓ [F0] L1709 [F2]
  rw [show [F0] ++ L1709 ++ [F2] = L1708 from rfl, show [F0] ++ L1709 = L1705 from rfl,
    show L1709 ++ [F2] = L1707 from rfl] at h
  rw [i886 hinj, i884 hinj, i885 hinj, i887 hinj] at h
  linarith

theorem row326 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1710 + (1 : ℝ) * HLm Γ 5 L1031 + (-1 : ℝ) * HLm Γ 5 L1713 + (-1 : ℝ) * HLm Γ 5 L1013 := by
  have h := HLm_submod hΓ [F7] L1715 [F3]
  rw [show [F7] ++ L1715 ++ [F3] = L1714 from rfl, show [F7] ++ L1715 = L1711 from rfl,
    show L1715 ++ [F3] = L1712 from rfl] at h
  rw [i890 hinj, i888 hinj, i889 hinj, i891 hinj] at h
  linarith

theorem row327 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1716 + (1 : ℝ) * HLm Γ 5 L1668 + (-1 : ℝ) * HLm Γ 5 L1719 + (-1 : ℝ) * HLm Γ 5 L993 := by
  have h := HLm_submod hΓ [F1] L1721 [F2]
  rw [show [F1] ++ L1721 ++ [F2] = L1720 from rfl, show [F1] ++ L1721 = L1717 from rfl,
    show L1721 ++ [F2] = L1718 from rfl] at h
  rw [i894 hinj, i892 hinj, i893 hinj, i895 hinj] at h
  linarith

theorem row328 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1723 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L995 := by
  have h := HLm_submod hΓ [F0] L996 [F2]
  rw [show [F0] ++ L996 ++ [F2] = L1725 from rfl, show [F0] ++ L996 = L1722 from rfl,
    show L996 ++ [F2] = L1724 from rfl] at h
  rw [i898 hinj, i896 hinj, i897 hinj, i463 hinj] at h
  linarith

theorem row329 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L997 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L995 := by
  have h := HLm_submod hΓ [F0] L996 [F25]
  rw [show [F0] ++ L996 ++ [F25] = L1727 from rfl, show [F0] ++ L996 = L1722 from rfl,
    show L996 ++ [F25] = L1726 from rfl] at h
  rw [i900 hinj, i896 hinj, i899 hinj, i463 hinj] at h
  linarith

theorem row330 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1728 + (1 : ℝ) * HLm Γ 5 L1015 + (-1 : ℝ) * HLm Γ 5 L1731 + (-1 : ℝ) * HLm Γ 5 L1005 := by
  have h := HLm_submod hΓ [F7] L1006 [F2]
  rw [show [F7] ++ L1006 ++ [F2] = L1732 from rfl, show [F7] ++ L1006 = L1729 from rfl,
    show L1006 ++ [F2] = L1730 from rfl] at h
  rw [i903 hinj, i901 hinj, i902 hinj, i468 hinj] at h
  linarith

theorem row331 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1734 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1737 := by
  have h := HLm_submod hΓ [F0] L1738 [F4]
  rw [show [F0] ++ L1738 ++ [F4] = L1736 from rfl, show [F0] ++ L1738 = L1733 from rfl,
    show L1738 ++ [F4] = L1735 from rfl] at h
  rw [i906 hinj, i904 hinj, i905 hinj, i907 hinj] at h
  linarith

theorem row332 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1323 + (1 : ℝ) * HLm Γ 5 L1057 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1055 := by
  have h := HLm_submod hΓ [F0] L1742 [F23]
  rw [show [F0] ++ L1742 ++ [F23] = L1741 from rfl, show [F0] ++ L1742 = L1739 from rfl,
    show L1742 ++ [F23] = L1740 from rfl] at h
  rw [i910 hinj, i908 hinj, i909 hinj, i911 hinj] at h
  linarith

theorem row333 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L916 + (1 : ℝ) * HLm Γ 5 L1133 + (-1 : ℝ) * HLm Γ 5 L1745 + (-1 : ℝ) * HLm Γ 5 L1747 := by
  have h := HLm_submod hΓ [F1] L1748 [F12]
  rw [show [F1] ++ L1748 ++ [F12] = L1746 from rfl, show [F1] ++ L1748 = L1743 from rfl,
    show L1748 ++ [F12] = L1744 from rfl] at h
  rw [i914 hinj, i912 hinj, i913 hinj, i915 hinj] at h
  linarith

theorem row334 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1749 + (1 : ℝ) * HLm Γ 5 L1099 + (-1 : ℝ) * HLm Γ 5 L1752 + (-1 : ℝ) * HLm Γ 5 L1097 := by
  have h := HLm_submod hΓ [F3] L1098 [F67]
  rw [show [F3] ++ L1098 ++ [F67] = L1753 from rfl, show [F3] ++ L1098 = L1750 from rfl,
    show L1098 ++ [F67] = L1751 from rfl] at h
  rw [i918 hinj, i916 hinj, i917 hinj, i519 hinj] at h
  linarith

theorem row335 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1754 + (1 : ℝ) * HLm Γ 5 L1756 + (-1 : ℝ) * HLm Γ 5 L1758 + (-1 : ℝ) * HLm Γ 5 L1760 := by
  have h := HLm_submod hΓ [F0] L1761 [F2]
  rw [show [F0] ++ L1761 ++ [F2] = L1759 from rfl, show [F0] ++ L1761 = L1755 from rfl,
    show L1761 ++ [F2] = L1757 from rfl] at h
  rw [i921 hinj, i919 hinj, i920 hinj, i922 hinj] at h
  linarith

theorem row336 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1762 + (1 : ℝ) * HLm Γ 5 L1025 + (-1 : ℝ) * HLm Γ 5 L1307 + (-1 : ℝ) * HLm Γ 5 L1148 := by
  have h := HLm_submod hΓ [F0] L1766 [F62]
  rw [show [F0] ++ L1766 ++ [F62] = L1765 from rfl, show [F0] ++ L1766 = L1763 from rfl,
    show L1766 ++ [F62] = L1764 from rfl] at h
  rw [i925 hinj, i923 hinj, i924 hinj, i926 hinj] at h
  linarith

theorem row337 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1767 + (1 : ℝ) * HLm Γ 5 L1769 + (-1 : ℝ) * HLm Γ 5 L1771 + (-1 : ℝ) * HLm Γ 5 L1773 := by
  have h := HLm_submod hΓ [F0] L1774 [F1]
  rw [show [F0] ++ L1774 ++ [F1] = L1772 from rfl, show [F0] ++ L1774 = L1768 from rfl,
    show L1774 ++ [F1] = L1770 from rfl] at h
  rw [i929 hinj, i927 hinj, i928 hinj, i930 hinj] at h
  linarith

theorem row338 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1093 + (1 : ℝ) * HLm Γ 5 L945 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L1117 := by
  have h := HLm_submod hΓ [F0] L1118 [F12]
  rw [show [F0] ++ L1118 ++ [F12] = L1777 from rfl, show [F0] ++ L1118 = L1775 from rfl,
    show L1118 ++ [F12] = L1776 from rfl] at h
  rw [i933 hinj, i931 hinj, i932 hinj, i530 hinj] at h
  linarith

theorem row339 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1778 + (1 : ℝ) * HLm Γ 5 L1155 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L1159 := by
  have h := HLm_submod hΓ [F0] L1782 [F12]
  rw [show [F0] ++ L1782 ++ [F12] = L1781 from rfl, show [F0] ++ L1782 = L1779 from rfl,
    show L1782 ++ [F12] = L1780 from rfl] at h
  rw [i936 hinj, i934 hinj, i935 hinj, i937 hinj] at h
  linarith

theorem row340 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1769 + (1 : ℝ) * HLm Γ 5 L1234 + (-1 : ℝ) * HLm Γ 5 L1785 + (-1 : ℝ) * HLm Γ 5 L1232 := by
  have h := HLm_submod hΓ [F1] L1787 [F62]
  rw [show [F1] ++ L1787 ++ [F62] = L1786 from rfl, show [F1] ++ L1787 = L1783 from rfl,
    show L1787 ++ [F62] = L1784 from rfl] at h
  rw [i940 hinj, i938 hinj, i939 hinj, i941 hinj] at h
  linarith

theorem row341 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L1251 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1239 := by
  have h := HLm_submod hΓ [F7] L1240 [F16]
  rw [show [F7] ++ L1240 ++ [F16] = L1789 from rfl, show [F7] ++ L1240 = L1242 from rfl,
    show L1240 ++ [F16] = L1788 from rfl] at h
  rw [i943 hinj, i601 hinj, i942 hinj, i600 hinj] at h
  linarith

theorem row342 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1791 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1298 := by
  have h := HLm_submod hΓ [F7] L1794 [F67]
  rw [show [F7] ++ L1794 ++ [F67] = L1793 from rfl, show [F7] ++ L1794 = L1790 from rfl,
    show L1794 ++ [F67] = L1792 from rfl] at h
  rw [i946 hinj, i944 hinj, i945 hinj, i947 hinj] at h
  linarith

theorem row343 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L1350 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1245 := by
  have h := HLm_submod hΓ [F7] L1246 [F16]
  rw [show [F7] ++ L1246 ++ [F16] = L1796 from rfl, show [F7] ++ L1246 = L1247 from rfl,
    show L1246 ++ [F16] = L1795 from rfl] at h
  rw [i949 hinj, i605 hinj, i948 hinj, i604 hinj] at h
  linarith

theorem row344 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1798 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1801 := by
  have h := HLm_submod hΓ [F1] L1802 [F67]
  rw [show [F1] ++ L1802 ++ [F67] = L1800 from rfl, show [F1] ++ L1802 = L1797 from rfl,
    show L1802 ++ [F67] = L1799 from rfl] at h
  rw [i952 hinj, i950 hinj, i951 hinj, i953 hinj] at h
  linarith

theorem row345 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1295 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1292 := by
  have h := HLm_submod hΓ [F1] L1806 [F67]
  rw [show [F1] ++ L1806 ++ [F67] = L1805 from rfl, show [F1] ++ L1806 = L1803 from rfl,
    show L1806 ++ [F67] = L1804 from rfl] at h
  rw [i956 hinj, i954 hinj, i955 hinj, i957 hinj] at h
  linarith

theorem row346 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1683 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1305 := by
  have h := HLm_submod hΓ [F1] L1810 [F67]
  rw [show [F1] ++ L1810 ++ [F67] = L1809 from rfl, show [F1] ++ L1810 = L1807 from rfl,
    show L1810 ++ [F67] = L1808 from rfl] at h
  rw [i960 hinj, i958 hinj, i959 hinj, i961 hinj] at h
  linarith

theorem row347 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1290 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1281 := by
  have h := HLm_submod hΓ [F1] L1814 [F67]
  rw [show [F1] ++ L1814 ++ [F67] = L1813 from rfl, show [F1] ++ L1814 = L1811 from rfl,
    show L1814 ++ [F67] = L1812 from rfl] at h
  rw [i964 hinj, i962 hinj, i963 hinj, i965 hinj] at h
  linarith

theorem row348 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1816 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1819 := by
  have h := HLm_submod hΓ [F1] L1820 [F67]
  rw [show [F1] ++ L1820 ++ [F67] = L1818 from rfl, show [F1] ++ L1820 = L1815 from rfl,
    show L1820 ++ [F67] = L1817 from rfl] at h
  rw [i968 hinj, i966 hinj, i967 hinj, i969 hinj] at h
  linarith

theorem row349 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1313 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1311 := by
  have h := HLm_submod hΓ [F1] L1824 [F67]
  rw [show [F1] ++ L1824 ++ [F67] = L1823 from rfl, show [F1] ++ L1824 = L1821 from rfl,
    show L1824 ++ [F67] = L1822 from rfl] at h
  rw [i972 hinj, i970 hinj, i971 hinj, i973 hinj] at h
  linarith

theorem row350 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L1321 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1319 := by
  have h := HLm_submod hΓ [F1] L1320 [F16]
  rw [show [F1] ++ L1320 ++ [F16] = L1827 from rfl, show [F1] ++ L1320 = L1825 from rfl,
    show L1320 ++ [F16] = L1826 from rfl] at h
  rw [i976 hinj, i974 hinj, i975 hinj, i649 hinj] at h
  linarith

theorem row351 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1301 + (1 : ℝ) * HLm Γ 5 L1264 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1339 := by
  have h := HLm_submod hΓ [F1] L1340 [F2]
  rw [show [F1] ++ L1340 ++ [F2] = L1830 from rfl, show [F1] ++ L1340 = L1828 from rfl,
    show L1340 ++ [F2] = L1829 from rfl] at h
  rw [i979 hinj, i977 hinj, i978 hinj, i660 hinj] at h
  linarith

theorem row352 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L1832 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1835 := by
  have h := HLm_submod hΓ [F1] L1836 [F7]
  rw [show [F1] ++ L1836 ++ [F7] = L1834 from rfl, show [F1] ++ L1836 = L1831 from rfl,
    show L1836 ++ [F7] = L1833 from rfl] at h
  rw [i982 hinj, i980 hinj, i981 hinj, i983 hinj] at h
  linarith

theorem row353 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1498 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1376 := by
  have h := HLm_submod hΓ [F0] L1840 [F67]
  rw [show [F0] ++ L1840 ++ [F67] = L1839 from rfl, show [F0] ++ L1840 = L1837 from rfl,
    show L1840 ++ [F67] = L1838 from rfl] at h
  rw [i986 hinj, i984 hinj, i985 hinj, i987 hinj] at h
  linarith

theorem row354 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1842 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1490 := by
  have h := HLm_submod hΓ [F0] L1845 [F67]
  rw [show [F0] ++ L1845 ++ [F67] = L1844 from rfl, show [F0] ++ L1845 = L1841 from rfl,
    show L1845 ++ [F67] = L1843 from rfl] at h
  rw [i990 hinj, i988 hinj, i989 hinj, i991 hinj] at h
  linarith

theorem row355 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L1731 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1360 := by
  have h := HLm_submod hΓ [F0] L1361 [F16]
  rw [show [F0] ++ L1361 ++ [F16] = L1847 from rfl, show [F0] ++ L1361 = L1362 from rfl,
    show L1361 ++ [F16] = L1846 from rfl] at h
  rw [i993 hinj, i678 hinj, i992 hinj, i677 hinj] at h
  linarith

theorem row356 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1849 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1852 := by
  have h := HLm_submod hΓ [F0] L1853 [F67]
  rw [show [F0] ++ L1853 ++ [F67] = L1851 from rfl, show [F0] ++ L1853 = L1848 from rfl,
    show L1853 ++ [F67] = L1850 from rfl] at h
  rw [i996 hinj, i994 hinj, i995 hinj, i997 hinj] at h
  linarith

theorem row357 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L1387 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1372 := by
  have h := HLm_submod hΓ [F0] L1373 [F16]
  rw [show [F0] ++ L1373 ++ [F16] = L1855 from rfl, show [F0] ++ L1373 = L1374 from rfl,
    show L1373 ++ [F16] = L1854 from rfl] at h
  rw [i999 hinj, i685 hinj, i998 hinj, i684 hinj] at h
  linarith

theorem row358 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L1713 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1398 := by
  have h := HLm_submod hΓ [F0] L1399 [F16]
  rw [show [F0] ++ L1399 ++ [F16] = L1857 from rfl, show [F0] ++ L1399 = L1400 from rfl,
    show L1399 ++ [F16] = L1856 from rfl] at h
  rw [i1001 hinj, i701 hinj, i1000 hinj, i700 hinj] at h
  linarith

theorem row359 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1449 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1445 := by
  have h := HLm_submod hΓ [F0] L1861 [F67]
  rw [show [F0] ++ L1861 ++ [F67] = L1860 from rfl, show [F0] ++ L1861 = L1858 from rfl,
    show L1861 ++ [F67] = L1859 from rfl] at h
  rw [i1004 hinj, i1002 hinj, i1003 hinj, i1005 hinj] at h
  linarith

theorem row360 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1862 + (1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1423 := by
  have h := HLm_submod hΓ [F1] L1866 [F0]
  rw [show [F1] ++ L1866 ++ [F0] = L1865 from rfl, show [F1] ++ L1866 = L1863 from rfl,
    show L1866 ++ [F0] = L1864 from rfl] at h
  rw [i1008 hinj, i1006 hinj, i1007 hinj, i1009 hinj] at h
  linarith

theorem row361 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1414 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1412 := by
  have h := HLm_submod hΓ [F0] L1413 [F67]
  rw [show [F0] ++ L1413 ++ [F67] = L1869 from rfl, show [F0] ++ L1413 = L1867 from rfl,
    show L1413 ++ [F67] = L1868 from rfl] at h
  rw [i1012 hinj, i1010 hinj, i1011 hinj, i708 hinj] at h
  linarith

theorem row362 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L1871 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1874 := by
  have h := HLm_submod hΓ [F1] L1875 [F0]
  rw [show [F1] ++ L1875 ++ [F0] = L1873 from rfl, show [F1] ++ L1875 = L1870 from rfl,
    show L1875 ++ [F0] = L1872 from rfl] at h
  rw [i1015 hinj, i1013 hinj, i1014 hinj, i1016 hinj] at h
  linarith

theorem row363 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L1626 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1879 := by
  have h := HLm_submod hΓ [F1] L1880 [F0]
  rw [show [F1] ++ L1880 ++ [F0] = L1878 from rfl, show [F1] ++ L1880 = L1876 from rfl,
    show L1880 ++ [F0] = L1877 from rfl] at h
  rw [i1019 hinj, i1017 hinj, i1018 hinj, i1020 hinj] at h
  linarith

theorem row364 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L1882 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1885 := by
  have h := HLm_submod hΓ [F1] L1886 [F0]
  rw [show [F1] ++ L1886 ++ [F0] = L1884 from rfl, show [F1] ++ L1886 = L1881 from rfl,
    show L1886 ++ [F0] = L1883 from rfl] at h
  rw [i1023 hinj, i1021 hinj, i1022 hinj, i1024 hinj] at h
  linarith

theorem row365 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1555 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1551 := by
  have h := HLm_submod hΓ [F0] L1552 [F67]
  rw [show [F0] ++ L1552 ++ [F67] = L1888 from rfl, show [F0] ++ L1552 = L1887 from rfl,
    show L1552 ++ [F67] = L1556 from rfl] at h
  rw [i1026 hinj, i1025 hinj, i794 hinj, i792 hinj] at h
  linarith

theorem row366 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1509 + (1 : ℝ) * HLm Γ 5 L1494 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1892 := by
  have h := HLm_submod hΓ [F0] L1893 [F7]
  rw [show [F0] ++ L1893 ++ [F7] = L1891 from rfl, show [F0] ++ L1893 = L1889 from rfl,
    show L1893 ++ [F7] = L1890 from rfl] at h
  rw [i1029 hinj, i1027 hinj, i1028 hinj, i1030 hinj] at h
  linarith

theorem row367 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1894 + (1 : ℝ) * HLm Γ 5 L1648 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1898 := by
  have h := HLm_submod hΓ [F0] L1899 [F12]
  rw [show [F0] ++ L1899 ++ [F12] = L1897 from rfl, show [F0] ++ L1899 = L1895 from rfl,
    show L1899 ++ [F12] = L1896 from rfl] at h
  rw [i1033 hinj, i1031 hinj, i1032 hinj, i1034 hinj] at h
  linarith

theorem row368 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1901 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1904 := by
  have h := HLm_submod hΓ [F0] L1905 [F67]
  rw [show [F0] ++ L1905 ++ [F67] = L1903 from rfl, show [F0] ++ L1905 = L1900 from rfl,
    show L1905 ++ [F67] = L1902 from rfl] at h
  rw [i1037 hinj, i1035 hinj, i1036 hinj, i1038 hinj] at h
  linarith

theorem row369 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1597 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1513 := by
  have h := HLm_submod hΓ [F0] L1909 [F67]
  rw [show [F0] ++ L1909 ++ [F67] = L1908 from rfl, show [F0] ++ L1909 = L1906 from rfl,
    show L1909 ++ [F67] = L1907 from rfl] at h
  rw [i1041 hinj, i1039 hinj, i1040 hinj, i1042 hinj] at h
  linarith

theorem row370 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1911 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1914 := by
  have h := HLm_submod hΓ [F0] L1915 [F67]
  rw [show [F0] ++ L1915 ++ [F67] = L1913 from rfl, show [F0] ++ L1915 = L1910 from rfl,
    show L1915 ++ [F67] = L1912 from rfl] at h
  rw [i1045 hinj, i1043 hinj, i1044 hinj, i1046 hinj] at h
  linarith

theorem row371 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1532 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1530 := by
  have h := HLm_submod hΓ [F0] L1919 [F67]
  rw [show [F0] ++ L1919 ++ [F67] = L1918 from rfl, show [F0] ++ L1919 = L1916 from rfl,
    show L1919 ++ [F67] = L1917 from rfl] at h
  rw [i1049 hinj, i1047 hinj, i1048 hinj, i1050 hinj] at h
  linarith

theorem row372 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1920 + (1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1542 := by
  have h := HLm_submod hΓ [F1] L1924 [F0]
  rw [show [F1] ++ L1924 ++ [F0] = L1923 from rfl, show [F1] ++ L1924 = L1921 from rfl,
    show L1924 ++ [F0] = L1922 from rfl] at h
  rw [i1053 hinj, i1051 hinj, i1052 hinj, i1054 hinj] at h
  linarith

theorem row373 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1926 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1929 := by
  have h := HLm_submod hΓ [F0] L1930 [F67]
  rw [show [F0] ++ L1930 ++ [F67] = L1928 from rfl, show [F0] ++ L1930 = L1925 from rfl,
    show L1930 ++ [F67] = L1927 from rfl] at h
  rw [i1057 hinj, i1055 hinj, i1056 hinj, i1058 hinj] at h
  linarith

theorem row374 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1932 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1935 := by
  have h := HLm_submod hΓ [F0] L1936 [F67]
  rw [show [F0] ++ L1936 ++ [F67] = L1934 from rfl, show [F0] ++ L1936 = L1931 from rfl,
    show L1936 ++ [F67] = L1933 from rfl] at h
  rw [i1061 hinj, i1059 hinj, i1060 hinj, i1062 hinj] at h
  linarith

theorem row375 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1654 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1650 := by
  have h := HLm_submod hΓ [F0] L1940 [F67]
  rw [show [F0] ++ L1940 ++ [F67] = L1939 from rfl, show [F0] ++ L1940 = L1937 from rfl,
    show L1940 ++ [F67] = L1938 from rfl] at h
  rw [i1065 hinj, i1063 hinj, i1064 hinj, i1066 hinj] at h
  linarith

theorem row376 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1661 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1659 := by
  have h := HLm_submod hΓ [F0] L1944 [F67]
  rw [show [F0] ++ L1944 ++ [F67] = L1943 from rfl, show [F0] ++ L1944 = L1941 from rfl,
    show L1944 ++ [F67] = L1942 from rfl] at h
  rw [i1069 hinj, i1067 hinj, i1068 hinj, i1070 hinj] at h
  linarith

theorem row377 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1406 + (1 : ℝ) * HLm Γ 5 L1672 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1670 := by
  have h := HLm_submod hΓ [F0] L1948 [F2]
  rw [show [F0] ++ L1948 ++ [F2] = L1947 from rfl, show [F0] ++ L1948 = L1945 from rfl,
    show L1948 ++ [F2] = L1946 from rfl] at h
  rw [i1073 hinj, i1071 hinj, i1072 hinj, i1074 hinj] at h
  linarith

theorem row378 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1949 + (1 : ℝ) * HLm Γ 5 L1442 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1953 := by
  have h := HLm_submod hΓ [F0] L1954 [F7]
  rw [show [F0] ++ L1954 ++ [F7] = L1952 from rfl, show [F0] ++ L1954 = L1950 from rfl,
    show L1954 ++ [F7] = L1951 from rfl] at h
  rw [i1077 hinj, i1075 hinj, i1076 hinj, i1078 hinj] at h
  linarith

theorem row379 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L1955 + (-1 : ℝ) * HLm Γ 5 L327 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F55]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F55] = L1957 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F55] = L1956 from rfl] at h
  rw [i1080 hinj, i1079 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row380 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L1958 + (-1 : ℝ) * HLm Γ 5 L91 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F43]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F43] = L91 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F43] = L1958 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row381 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L28 + (-1 : ℝ) * HLm Γ 5 L611 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F11]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F11] = L611 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F11] = L28 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row382 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1 + (1 : ℝ) * HLm Γ 5 L63 + (-1 : ℝ) * HLm Γ 5 L297 := by
  have h := HLm_submod hΓ [F1] ([] : List (Form 5)) [F27]
  rw [show [F1] ++ ([] : List (Form 5)) ++ [F27] = L298 from rfl, show [F1] ++ ([] : List (Form 5)) = L1 from rfl,
    show ([] : List (Form 5)) ++ [F27] = L63 from rfl] at h
  rw [i114 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row383 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L22 + (1 : ℝ) * HLm Γ 5 L1958 + (-1 : ℝ) * HLm Γ 5 L526 := by
  have h := HLm_submod hΓ [F9] ([] : List (Form 5)) [F43]
  rw [show [F9] ++ ([] : List (Form 5)) ++ [F43] = L526 from rfl, show [F9] ++ ([] : List (Form 5)) = L22 from rfl,
    show ([] : List (Form 5)) ++ [F43] = L1958 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row384 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L1959 + (-1 : ℝ) * HLm Γ 5 L1960 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F108]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F108] = L1961 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F108] = L1959 from rfl] at h
  rw [i1081 hinj, i5 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row385 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L1955 + (-1 : ℝ) * HLm Γ 5 L157 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F55]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F55] = L1962 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F55] = L1956 from rfl] at h
  rw [i1082 hinj, i5 hinj, i1079 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row386 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L13 + (-1 : ℝ) * HLm Γ 5 L679 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F6]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F6] = L1963 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F6] = L13 from rfl] at h
  rw [i1083 hinj, i5 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row387 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L31 + (1 : ℝ) * HLm Γ 5 L69 + (-1 : ℝ) * HLm Γ 5 L1964 := by
  have h := HLm_submod hΓ [F12] ([] : List (Form 5)) [F31]
  rw [show [F12] ++ ([] : List (Form 5)) ++ [F31] = L1965 from rfl, show [F12] ++ ([] : List (Form 5)) = L31 from rfl,
    show ([] : List (Form 5)) ++ [F31] = L69 from rfl] at h
  rw [i1084 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row388 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1966 + (1 : ℝ) * HLm Γ 5 L38 + (-1 : ℝ) * HLm Γ 5 L1967 := by
  have h := HLm_submod hΓ [F111] ([] : List (Form 5)) [F16]
  rw [show [F111] ++ ([] : List (Form 5)) ++ [F16] = L1967 from rfl, show [F111] ++ ([] : List (Form 5)) = L1966 from rfl,
    show ([] : List (Form 5)) ++ [F16] = L38 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row389 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L204 + (1 : ℝ) * HLm Γ 5 L38 + (-1 : ℝ) * HLm Γ 5 L210 := by
  have h := HLm_submod hΓ [F46] ([] : List (Form 5)) [F16]
  rw [show [F46] ++ ([] : List (Form 5)) ++ [F16] = L210 from rfl, show [F46] ++ ([] : List (Form 5)) = L204 from rfl,
    show ([] : List (Form 5)) ++ [F16] = L38 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row390 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L38 + (1 : ℝ) * HLm Γ 5 L59 + (-1 : ℝ) * HLm Γ 5 L1968 := by
  have h := HLm_submod hΓ [F16] ([] : List (Form 5)) [F25]
  rw [show [F16] ++ ([] : List (Form 5)) ++ [F25] = L1969 from rfl, show [F16] ++ ([] : List (Form 5)) = L38 from rfl,
    show ([] : List (Form 5)) ++ [F25] = L59 from rfl] at h
  rw [i1085 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row391 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L51 + (1 : ℝ) * HLm Γ 5 L1970 + (-1 : ℝ) * HLm Γ 5 L1971 := by
  have h := HLm_submod hΓ [F21] ([] : List (Form 5)) [F117]
  rw [show [F21] ++ ([] : List (Form 5)) ++ [F117] = L1971 from rfl, show [F21] ++ ([] : List (Form 5)) = L51 from rfl,
    show ([] : List (Form 5)) ++ [F117] = L1970 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row392 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L53 + (1 : ℝ) * HLm Γ 5 L1972 + (-1 : ℝ) * HLm Γ 5 L1973 := by
  have h := HLm_submod hΓ [F22] ([] : List (Form 5)) [F183]
  rw [show [F22] ++ ([] : List (Form 5)) ++ [F183] = L1974 from rfl, show [F22] ++ ([] : List (Form 5)) = L53 from rfl,
    show ([] : List (Form 5)) ++ [F183] = L1972 from rfl] at h
  rw [i1086 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row393 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11 + (1 : ℝ) * HLm Γ 5 L42 + (-1 : ℝ) * HLm Γ 5 L1975 := by
  have h := HLm_submod hΓ [F5] ([] : List (Form 5)) [F18]
  rw [show [F5] ++ ([] : List (Form 5)) ++ [F18] = L1976 from rfl, show [F5] ++ ([] : List (Form 5)) = L11 from rfl,
    show ([] : List (Form 5)) ++ [F18] = L42 from rfl] at h
  rw [i1087 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row394 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L39 + (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F17] ([] : List (Form 5)) [F45]
  rw [show [F17] ++ ([] : List (Form 5)) ++ [F45] = L273 from rfl, show [F17] ++ ([] : List (Form 5)) = L39 from rfl,
    show ([] : List (Form 5)) ++ [F45] = L456 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row395 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L39 + (1 : ℝ) * HLm Γ 5 L461 + (-1 : ℝ) * HLm Γ 5 L1977 := by
  have h := HLm_submod hΓ [F17] ([] : List (Form 5)) [F48]
  rw [show [F17] ++ ([] : List (Form 5)) ++ [F48] = L1977 from rfl, show [F17] ++ ([] : List (Form 5)) = L39 from rfl,
    show ([] : List (Form 5)) ++ [F48] = L461 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row396 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L68 + (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm Γ 5 L1978 := by
  have h := HLm_submod hΓ [F30] ([] : List (Form 5)) [F19]
  rw [show [F30] ++ ([] : List (Form 5)) ++ [F19] = L1978 from rfl, show [F30] ++ ([] : List (Form 5)) = L68 from rfl,
    show ([] : List (Form 5)) ++ [F19] = L45 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row397 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L72 + (1 : ℝ) * HLm Γ 5 L549 + (-1 : ℝ) * HLm Γ 5 L1979 := by
  have h := HLm_submod hΓ [F33] ([] : List (Form 5)) [F105]
  rw [show [F33] ++ ([] : List (Form 5)) ++ [F105] = L1979 from rfl, show [F33] ++ ([] : List (Form 5)) = L72 from rfl,
    show ([] : List (Form 5)) ++ [F105] = L549 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row398 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L73 + (1 : ℝ) * HLm Γ 5 L19 + (-1 : ℝ) * HLm Γ 5 L1980 := by
  have h := HLm_submod hΓ [F34] ([] : List (Form 5)) [F8]
  rw [show [F34] ++ ([] : List (Form 5)) ++ [F8] = L1981 from rfl, show [F34] ++ ([] : List (Form 5)) = L73 from rfl,
    show ([] : List (Form 5)) ++ [F8] = L19 from rfl] at h
  rw [i1088 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row399 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L60 + (1 : ℝ) * HLm Γ 5 L34 + (-1 : ℝ) * HLm Γ 5 L1982 := by
  have h := HLm_submod hΓ [F26] ([] : List (Form 5)) [F14]
  rw [show [F26] ++ ([] : List (Form 5)) ++ [F14] = L1982 from rfl, show [F26] ++ ([] : List (Form 5)) = L60 from rfl,
    show ([] : List (Form 5)) ++ [F14] = L34 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row400 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L69 + (1 : ℝ) * HLm Γ 5 L503 + (-1 : ℝ) * HLm Γ 5 L1983 := by
  have h := HLm_submod hΓ [F31] ([] : List (Form 5)) [F72]
  rw [show [F31] ++ ([] : List (Form 5)) ++ [F72] = L1983 from rfl, show [F31] ++ ([] : List (Form 5)) = L69 from rfl,
    show ([] : List (Form 5)) ++ [F72] = L503 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row401 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6 + (1 : ℝ) * HLm Γ 5 L1985 + (-1 : ℝ) * HLm Γ 5 L1986 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F3] L0 [F13]
  rw [show [F3] ++ L0 ++ [F13] = L1987 from rfl, show [F3] ++ L0 = L1984 from rfl,
    show L0 ++ [F13] = L1985 from rfl] at h
  rw [i1090 hinj, i1089 hinj] at h
  linarith

theorem row402 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L120 + (1 : ℝ) * HLm Γ 5 L1988 + (-1 : ℝ) * HLm Γ 5 L1990 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F48] L15 [F59]
  rw [show [F48] ++ L15 ++ [F59] = L1991 from rfl, show [F48] ++ L15 = L121 from rfl,
    show L15 ++ [F59] = L1989 from rfl] at h
  rw [i1092 hinj, i34 hinj, i1091 hinj] at h
  linarith

theorem row403 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L677 + (1 : ℝ) * HLm Γ 5 L1988 + (-1 : ℝ) * HLm Γ 5 L1992 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F26] L15 [F59]
  rw [show [F26] ++ L15 ++ [F59] = L1993 from rfl, show [F26] ++ L15 = L677 from rfl,
    show L15 ++ [F59] = L1989 from rfl] at h
  rw [i1093 hinj, i1091 hinj] at h
  linarith

theorem row404 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1994 + (1 : ℝ) * HLm Γ 5 L532 + (-1 : ℝ) * HLm Γ 5 L1995 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F31] L15 [F39]
  rw [show [F31] ++ L15 ++ [F39] = L1996 from rfl, show [F31] ++ L15 = L1994 from rfl,
    show L15 ++ [F39] = L685 from rfl] at h
  rw [i1094 hinj, i298 hinj] at h
  linarith

theorem row405 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2 + (1 : ℝ) * HLm Γ 5 L1998 + (-1 : ℝ) * HLm Γ 5 L1999 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F0] L136 [F48]
  rw [show [F0] ++ L136 ++ [F48] = L2000 from rfl, show [F0] ++ L136 = L1997 from rfl,
    show L136 ++ [F48] = L1998 from rfl] at h
  rw [i1096 hinj, i1095 hinj] at h
  linarith

theorem row406 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2001 + (1 : ℝ) * HLm Γ 5 L2003 + (-1 : ℝ) * HLm Γ 5 L1395 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F7] L136 [F6]
  rw [show [F7] ++ L136 ++ [F6] = L1396 from rfl, show [F7] ++ L136 = L2002 from rfl,
    show L136 ++ [F6] = L2003 from rfl] at h
  rw [i698 hinj, i1097 hinj] at h
  linarith

theorem row407 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2004 + (1 : ℝ) * HLm Γ 5 L2006 + (-1 : ℝ) * HLm Γ 5 L2008 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F45] L147 [F50]
  rw [show [F45] ++ L147 ++ [F50] = L2009 from rfl, show [F45] ++ L147 = L2005 from rfl,
    show L147 ++ [F50] = L2007 from rfl] at h
  rw [i1100 hinj, i1098 hinj, i1099 hinj] at h
  linarith

theorem row408 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L827 + (-1 : ℝ) * HLm Γ 5 L679 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F0] L22 [F6]
  rw [show [F0] ++ L22 ++ [F6] = L822 from rfl, show [F0] ++ L22 = L154 from rfl,
    show L22 ++ [F6] = L827 from rfl] at h
  rw [i370 hinj, i49 hinj] at h
  linarith

theorem row409 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2010 + (1 : ℝ) * HLm Γ 5 L801 + (-1 : ℝ) * HLm Γ 5 L2012 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F1] L22 [F45]
  rw [show [F1] ++ L22 ++ [F45] = L2013 from rfl, show [F1] ++ L22 = L2011 from rfl,
    show L22 ++ [F45] = L801 from rfl] at h
  rw [i1102 hinj, i1101 hinj] at h
  linarith

theorem row410 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2014 + (1 : ℝ) * HLm Γ 5 L168 + (-1 : ℝ) * HLm Γ 5 L2016 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F3] L22 [F22]
  rw [show [F3] ++ L22 ++ [F22] = L2017 from rfl, show [F3] ++ L22 = L2015 from rfl,
    show L22 ++ [F22] = L769 from rfl] at h
  rw [i1104 hinj, i1103 hinj, i341 hinj] at h
  linarith

theorem row411 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2014 + (1 : ℝ) * HLm Γ 5 L174 + (-1 : ℝ) * HLm Γ 5 L2018 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F3] L22 [F26]
  rw [show [F3] ++ L22 ++ [F26] = L2019 from rfl, show [F3] ++ L22 = L2015 from rfl,
    show L22 ++ [F26] = L175 from rfl] at h
  rw [i1105 hinj, i1103 hinj, i59 hinj] at h
  linarith

theorem row412 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2020 + (1 : ℝ) * HLm Γ 5 L33 + (-1 : ℝ) * HLm Γ 5 L2022 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F1] L31 [F13]
  rw [show [F1] ++ L31 ++ [F13] = L2023 from rfl, show [F1] ++ L31 = L2021 from rfl,
    show L31 ++ [F13] = L33 from rfl] at h
  rw [i1107 hinj, i1106 hinj] at h
  linarith

theorem row413 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2020 + (1 : ℝ) * HLm Γ 5 L190 + (-1 : ℝ) * HLm Γ 5 L2024 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F1] L31 [F6]
  rw [show [F1] ++ L31 ++ [F6] = L2025 from rfl, show [F1] ++ L31 = L2021 from rfl,
    show L31 ++ [F6] = L191 from rfl] at h
  rw [i1108 hinj, i1106 hinj, i66 hinj] at h
  linarith

theorem row414 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L180 + (1 : ℝ) * HLm Γ 5 L2027 + (-1 : ℝ) * HLm Γ 5 L2029 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F16] L31 [F29]
  rw [show [F16] ++ L31 ++ [F29] = L2030 from rfl, show [F16] ++ L31 = L2026 from rfl,
    show L31 ++ [F29] = L2028 from rfl] at h
  rw [i1111 hinj, i1109 hinj, i1110 hinj] at h
  linarith

theorem row415 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1967 + (1 : ℝ) * HLm Γ 5 L2032 + (-1 : ℝ) * HLm Γ 5 L2034 + (-1 : ℝ) * HLm Γ 5 L1966 := by
  have h := HLm_submod hΓ [F16] L1966 [F52]
  rw [show [F16] ++ L1966 ++ [F52] = L2035 from rfl, show [F16] ++ L1966 = L2031 from rfl,
    show L1966 ++ [F52] = L2033 from rfl] at h
  rw [i1114 hinj, i1112 hinj, i1113 hinj] at h
  linarith

theorem row416 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L216 + (1 : ℝ) * HLm Γ 5 L2037 + (-1 : ℝ) * HLm Γ 5 L218 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F16] L199 [F67]
  rw [show [F16] ++ L199 ++ [F67] = L2038 from rfl, show [F16] ++ L199 = L2036 from rfl,
    show L199 ++ [F67] = L2037 from rfl] at h
  rw [i1116 hinj, i1115 hinj] at h
  linarith

theorem row417 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L99 + (1 : ℝ) * HLm Γ 5 L206 + (-1 : ℝ) * HLm Γ 5 L2039 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F0] L204 [F13]
  rw [show [F0] ++ L204 ++ [F13] = L2040 from rfl, show [F0] ++ L204 = L99 from rfl,
    show L204 ++ [F13] = L207 from rfl] at h
  rw [i1117 hinj, i72 hinj] at h
  linarith

theorem row418 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L210 + (1 : ℝ) * HLm Γ 5 L2041 + (-1 : ℝ) * HLm Γ 5 L934 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F16] L204 [F24]
  rw [show [F16] ++ L204 ++ [F24] = L2043 from rfl, show [F16] ++ L204 = L211 from rfl,
    show L204 ++ [F24] = L2042 from rfl] at h
  rw [i1119 hinj, i74 hinj, i1118 hinj] at h
  linarith

theorem row419 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L103 + (1 : ℝ) * HLm Γ 5 L222 + (-1 : ℝ) * HLm Γ 5 L1276 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F0] L51 [F4]
  rw [show [F0] ++ L51 ++ [F4] = L2046 from rfl, show [F0] ++ L51 = L2044 from rfl,
    show L51 ++ [F4] = L2045 from rfl] at h
  rw [i1122 hinj, i1120 hinj, i1121 hinj] at h
  linarith

theorem row420 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L103 + (1 : ℝ) * HLm Γ 5 L1971 + (-1 : ℝ) * HLm Γ 5 L2047 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F0] L51 [F117]
  rw [show [F0] ++ L51 ++ [F117] = L2048 from rfl, show [F0] ++ L51 = L2044 from rfl,
    show L51 ++ [F117] = L1971 from rfl] at h
  rw [i1123 hinj, i1120 hinj] at h
  linarith

theorem row421 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L303 + (1 : ℝ) * HLm Γ 5 L2049 + (-1 : ℝ) * HLm Γ 5 L305 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F7] L51 [F23]
  rw [show [F7] ++ L51 ++ [F23] = L2050 from rfl, show [F7] ++ L51 = L635 from rfl,
    show L51 ++ [F23] = L2049 from rfl] at h
  rw [i1124 hinj, i273 hinj] at h
  linarith

theorem row422 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2051 + (1 : ℝ) * HLm Γ 5 L2053 + (-1 : ℝ) * HLm Γ 5 L2055 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F3] L51 [F24]
  rw [show [F3] ++ L51 ++ [F24] = L2056 from rfl, show [F3] ++ L51 = L2052 from rfl,
    show L51 ++ [F24] = L2054 from rfl] at h
  rw [i1127 hinj, i1125 hinj, i1126 hinj] at h
  linarith

theorem row423 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2051 + (1 : ℝ) * HLm Γ 5 L224 + (-1 : ℝ) * HLm Γ 5 L2057 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F3] L51 [F13]
  rw [show [F3] ++ L51 ++ [F13] = L2058 from rfl, show [F3] ++ L51 = L2052 from rfl,
    show L51 ++ [F13] = L224 from rfl] at h
  rw [i1128 hinj, i1125 hinj] at h
  linarith

theorem row424 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2059 + (1 : ℝ) * HLm Γ 5 L55 + (-1 : ℝ) * HLm Γ 5 L2061 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F62] L53 [F23]
  rw [show [F62] ++ L53 ++ [F23] = L2062 from rfl, show [F62] ++ L53 = L2060 from rfl,
    show L53 ++ [F23] = L55 from rfl] at h
  rw [i1130 hinj, i1129 hinj] at h
  linarith

theorem row425 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L234 + (1 : ℝ) * HLm Γ 5 L241 + (-1 : ℝ) * HLm Γ 5 L1175 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F3] L53 [F67]
  rw [show [F3] ++ L53 ++ [F67] = L2064 from rfl, show [F3] ++ L53 = L2063 from rfl,
    show L53 ++ [F67] = L241 from rfl] at h
  rw [i1132 hinj, i1131 hinj] at h
  linarith

theorem row426 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1190 + (1 : ℝ) * HLm Γ 5 L991 + (-1 : ℝ) * HLm Γ 5 L2066 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F4] L53 [F68]
  rw [show [F4] ++ L53 ++ [F68] = L2067 from rfl, show [F4] ++ L53 = L2065 from rfl,
    show L53 ++ [F68] = L992 from rfl] at h
  rw [i1134 hinj, i1133 hinj, i461 hinj] at h
  linarith

theorem row427 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L241 + (1 : ℝ) * HLm Γ 5 L1009 + (-1 : ℝ) * HLm Γ 5 L2068 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F67] L53 [F17]
  rw [show [F67] ++ L53 ++ [F17] = L2069 from rfl, show [F67] ++ L53 = L242 from rfl,
    show L53 ++ [F17] = L1010 from rfl] at h
  rw [i1135 hinj, i87 hinj, i470 hinj] at h
  linarith

theorem row428 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L248 + (1 : ℝ) * HLm Γ 5 L497 + (-1 : ℝ) * HLm Γ 5 L2070 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F31] L53 [F39]
  rw [show [F31] ++ L53 ++ [F39] = L2071 from rfl, show [F31] ++ L53 = L248 from rfl,
    show L53 ++ [F39] = L1052 from rfl] at h
  rw [i1136 hinj, i493 hinj] at h
  linarith

theorem row429 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L252 + (1 : ℝ) * HLm Γ 5 L1977 + (-1 : ℝ) * HLm Γ 5 L2072 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F0] L39 [F48]
  rw [show [F0] ++ L39 ++ [F48] = L2073 from rfl, show [F0] ++ L39 = L253 from rfl,
    show L39 ++ [F48] = L1977 from rfl] at h
  rw [i1137 hinj, i92 hinj] at h
  linarith

theorem row430 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L265 + (1 : ℝ) * HLm Γ 5 L1982 + (-1 : ℝ) * HLm Γ 5 L2075 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F2] L39 [F26]
  rw [show [F2] ++ L39 ++ [F26] = L2076 from rfl, show [F2] ++ L39 = L266 from rfl,
    show L39 ++ [F26] = L2074 from rfl] at h
  rw [i1139 hinj, i99 hinj, i1138 hinj] at h
  linarith

theorem row431 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L288 + (1 : ℝ) * HLm Γ 5 L1968 + (-1 : ℝ) * HLm Γ 5 L2077 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F0] L59 [F16]
  rw [show [F0] ++ L59 ++ [F16] = L2077 from rfl, show [F0] ++ L59 = L288 from rfl,
    show L59 ++ [F16] = L1968 from rfl] at h
  linarith

theorem row432 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2078 + (1 : ℝ) * HLm Γ 5 L452 + (-1 : ℝ) * HLm Γ 5 L2080 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F44] L59 [F45]
  rw [show [F44] ++ L59 ++ [F45] = L2081 from rfl, show [F44] ++ L59 = L2079 from rfl,
    show L59 ++ [F45] = L452 from rfl] at h
  rw [i1141 hinj, i1140 hinj] at h
  linarith

theorem row433 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1968 + (1 : ℝ) * HLm Γ 5 L2082 + (-1 : ℝ) * HLm Γ 5 L454 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F16] L59 [F67]
  rw [show [F16] ++ L59 ++ [F67] = L2083 from rfl, show [F16] ++ L59 = L1969 from rfl,
    show L59 ++ [F67] = L2082 from rfl] at h
  rw [i1142 hinj, i1085 hinj] at h
  linarith

theorem row434 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2084 + (1 : ℝ) * HLm Γ 5 L2085 + (-1 : ℝ) * HLm Γ 5 L2087 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F21] L59 [F23]
  rw [show [F21] ++ L59 ++ [F23] = L2088 from rfl, show [F21] ++ L59 = L2084 from rfl,
    show L59 ++ [F23] = L2086 from rfl] at h
  rw [i1144 hinj, i1143 hinj] at h
  linarith

theorem row435 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L297 + (1 : ℝ) * HLm Γ 5 L303 + (-1 : ℝ) * HLm Γ 5 L2090 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F1] L63 [F7]
  rw [show [F1] ++ L63 ++ [F7] = L2091 from rfl, show [F1] ++ L63 = L298 from rfl,
    show L63 ++ [F7] = L2089 from rfl] at h
  rw [i1146 hinj, i114 hinj, i1145 hinj] at h
  linarith

theorem row436 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L303 + (1 : ℝ) * HLm Γ 5 L312 + (-1 : ℝ) * HLm Γ 5 L619 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F7] L63 [F3]
  rw [show [F7] ++ L63 ++ [F3] = L2092 from rfl, show [F7] ++ L63 = L304 from rfl,
    show L63 ++ [F3] = L312 from rfl] at h
  rw [i1147 hinj, i117 hinj] at h
  linarith

theorem row437 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L360 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L2094 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F3] L332 [F67]
  rw [show [F3] ++ L332 ++ [F67] = L2095 from rfl, show [F3] ++ L332 = L2093 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i1149 hinj, i1148 hinj] at h
  linarith

theorem row438 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L180 + (1 : ℝ) * HLm Γ 5 L1978 + (-1 : ℝ) * HLm Γ 5 L1152 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F12] L68 [F19]
  rw [show [F12] ++ L68 ++ [F19] = L2097 from rfl, show [F12] ++ L68 = L2096 from rfl,
    show L68 ++ [F19] = L1978 from rfl] at h
  rw [i1151 hinj, i1150 hinj] at h
  linarith

theorem row439 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L354 + (1 : ℝ) * HLm Γ 5 L2098 + (-1 : ℝ) * HLm Γ 5 L2100 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F62] L68 [F45]
  rw [show [F62] ++ L68 ++ [F45] = L2101 from rfl, show [F62] ++ L68 = L355 from rfl,
    show L68 ++ [F45] = L2099 from rfl] at h
  rw [i1153 hinj, i140 hinj, i1152 hinj] at h
  linarith

theorem row440 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L382 + (1 : ℝ) * HLm Γ 5 L2102 + (-1 : ℝ) * HLm Γ 5 L2103 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F9] L387 [F82]
  rw [show [F9] ++ L387 ++ [F82] = L2104 from rfl, show [F9] ++ L387 = L383 from rfl,
    show L387 ++ [F82] = L2102 from rfl] at h
  rw [i1154 hinj, i154 hinj] at h
  linarith

theorem row441 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L878 + (1 : ℝ) * HLm Γ 5 L2105 + (-1 : ℝ) * HLm Γ 5 L2107 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F12] L387 [F19]
  rw [show [F12] ++ L387 ++ [F19] = L2108 from rfl, show [F12] ++ L387 = L878 from rfl,
    show L387 ++ [F19] = L2106 from rfl] at h
  rw [i1156 hinj, i1155 hinj] at h
  linarith

theorem row442 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2109 + (1 : ℝ) * HLm Γ 5 L2111 + (-1 : ℝ) * HLm Γ 5 L2113 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F62] L72 [F183]
  rw [show [F62] ++ L72 ++ [F183] = L2114 from rfl, show [F62] ++ L72 = L2110 from rfl,
    show L72 ++ [F183] = L2112 from rfl] at h
  rw [i1159 hinj, i1157 hinj, i1158 hinj] at h
  linarith

theorem row443 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2115 + (1 : ℝ) * HLm Γ 5 L2117 + (-1 : ℝ) * HLm Γ 5 L2118 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F23] L72 [F88]
  rw [show [F23] ++ L72 ++ [F88] = L2119 from rfl, show [F23] ++ L72 = L2116 from rfl,
    show L72 ++ [F88] = L2117 from rfl] at h
  rw [i1161 hinj, i1160 hinj] at h
  linarith

theorem row444 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L393 + (1 : ℝ) * HLm Γ 5 L2120 + (-1 : ℝ) * HLm Γ 5 L2122 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F0] L73 [F29]
  rw [show [F0] ++ L73 ++ [F29] = L2123 from rfl, show [F0] ++ L73 = L393 from rfl,
    show L73 ++ [F29] = L2121 from rfl] at h
  rw [i1163 hinj, i1162 hinj] at h
  linarith

theorem row445 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2124 + (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L1180 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F62] L73 [F67]
  rw [show [F62] ++ L73 ++ [F67] = L2127 from rfl, show [F62] ++ L73 = L2125 from rfl,
    show L73 ++ [F67] = L2126 from rfl] at h
  rw [i1165 hinj, i1164 hinj] at h
  linarith

theorem row446 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L398 + (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L2128 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F16] L73 [F67]
  rw [show [F16] ++ L73 ++ [F67] = L2129 from rfl, show [F16] ++ L73 = L399 from rfl,
    show L73 ++ [F67] = L2126 from rfl] at h
  rw [i1166 hinj, i160 hinj] at h
  linarith

theorem row447 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2130 + (1 : ℝ) * HLm Γ 5 L79 + (-1 : ℝ) * HLm Γ 5 L2132 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F2] L76 [F38]
  rw [show [F2] ++ L76 ++ [F38] = L2133 from rfl, show [F2] ++ L76 = L2131 from rfl,
    show L76 ++ [F38] = L80 from rfl] at h
  rw [i1168 hinj, i1167 hinj, i18 hinj] at h
  linarith

theorem row448 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L103 + (1 : ℝ) * HLm Γ 5 L2135 + (-1 : ℝ) * HLm Γ 5 L1280 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F0] L428 [F3]
  rw [show [F0] ++ L428 ++ [F3] = L2137 from rfl, show [F0] ++ L428 = L2134 from rfl,
    show L428 ++ [F3] = L2136 from rfl] at h
  rw [i1171 hinj, i1169 hinj, i1170 hinj, i174 hinj] at h
  linarith

theorem row449 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L646 + (1 : ℝ) * HLm Γ 5 L445 + (-1 : ℝ) * HLm Γ 5 L2139 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F7] L428 [F87]
  rw [show [F7] ++ L428 ++ [F87] = L2140 from rfl, show [F7] ++ L428 = L647 from rfl,
    show L428 ++ [F87] = L2138 from rfl] at h
  rw [i1173 hinj, i279 hinj, i1172 hinj, i174 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
