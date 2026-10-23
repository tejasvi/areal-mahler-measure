import ArealUK.Chunk1700
import ArealUK.Chunk1701
import ArealUK.Chunk1702
import ArealUK.Chunk1703
import ArealUK.Chunk1704
import ArealUK.Chunk1705
import ArealUK.Chunk1706
import ArealUK.Chunk1707
import ArealUK.Chunk1708
import ArealUK.Chunk1709
import ArealUK.Chunk1710
import ArealUK.Chunk1711
import ArealUK.Chunk1712
import ArealUK.Chunk1713
import ArealUK.Chunk1714
import ArealUK.Chunk1715
import ArealUK.Chunk1716
import ArealUK.Chunk1717
import ArealUK.Chunk1718
import ArealUK.Chunk1719
import ArealUK.Chunk1720
import ArealUK.Chunk1721
import ArealUK.Chunk1722
import ArealUK.Chunk1723
import ArealUK.Chunk1724
import ArealUK.Chunk1725
import ArealUK.Chunk1726
import ArealUK.Chunk1727
import ArealUK.Chunk1728
import ArealUK.Chunk1729
import ArealUK.Chunk1730
import ArealUK.Chunk1731
import ArealUK.Chunk1732
import ArealUK.Chunk1733
import ArealUK.Chunk1734
import ArealUK.Chunk1735
import ArealUK.Chunk1736
import ArealUK.Chunk1737
import ArealUK.Chunk1738
import ArealUK.Chunk1739
import ArealUK.Chunk1740
import ArealUK.Chunk1741
import ArealUK.Chunk1742
import ArealUK.Chunk1743
import ArealUK.Chunk1744
import ArealUK.Chunk1745
import ArealUK.Chunk1746
import ArealUK.Chunk1747
import ArealUK.Chunk1748
import ArealUK.Chunk1749
import ArealUK.Chunk1750
import ArealUK.Chunk1751
import ArealUK.Chunk1752
import ArealUK.Chunk1753
import ArealUK.Chunk1754
import ArealUK.Chunk1755
import ArealUK.Chunk1756
import ArealUK.Chunk1757
import ArealUK.Chunk1758
import ArealUK.Chunk1759
import ArealUK.Chunk1760
import ArealUK.Chunk1761
import ArealUK.Chunk1762
import ArealUK.Chunk1763
import ArealUK.Chunk1764
import ArealUK.Chunk1765
import ArealUK.Chunk1766
import ArealUK.Chunk1767
import ArealUK.Chunk1768
import ArealUK.Chunk1769
import ArealUK.Chunk1770
import ArealUK.Chunk1771
import ArealUK.Chunk1772
import ArealUK.Chunk1773
import ArealUK.Chunk1774
import ArealUK.Chunk1775
import ArealUK.Chunk1776
import ArealUK.Chunk1777
import ArealUK.Chunk1778
import ArealUK.Chunk1779
import ArealUK.Chunk1780
import ArealUK.Chunk1781
import ArealUK.Chunk1782
import ArealUK.Chunk1783
import ArealUK.Chunk1784
import ArealUK.Chunk1785
import ArealUK.Chunk1786
import ArealUK.Chunk1787
import ArealUK.Chunk1788
import ArealUK.Chunk1789
import ArealUK.Chunk1790
import ArealUK.Chunk1791
import ArealUK.Chunk1792
import ArealUK.Chunk1793
import ArealUK.Chunk1794
import ArealUK.Chunk1795
import ArealUK.Chunk1796
import ArealUK.Chunk1797
import ArealUK.Chunk1798
import ArealUK.Chunk1799
import Areal.UCert.LeavesKGen

/-! Group 17 of the upper K tiling shards. Generated inline. -/

namespace Areal.UCert

open ArealUCore

theorem group_17 : leavesOK ctxLitU 57312500000 3 ((leaves.drop 3400).take 200) 59437500000 3 = true := by
  have s99 := ArealUCore.ArealUK.chunk_1799
  have s98 : leavesOK ctxLitU 118825000000 4 ((leaves.drop 3596).take 4) 59437500000 3 = true :=
    take_step (n := 2) (t := 4) (b := 3598) rfl rfl ArealUCore.ArealUK.chunk_1798 s99
  have s97 : leavesOK ctxLitU 118800000000 4 ((leaves.drop 3594).take 6) 59437500000 3 = true :=
    take_step (n := 2) (t := 6) (b := 3596) rfl rfl ArealUCore.ArealUK.chunk_1797 s98
  have s96 : leavesOK ctxLitU 121525420327408 14 ((leaves.drop 3592).take 8) 59437500000 3 = true :=
    take_step (n := 2) (t := 8) (b := 3594) rfl rfl ArealUCore.ArealUK.chunk_1796 s97
  have s95 : leavesOK ctxLitU 30349910163701 12 ((leaves.drop 3590).take 10) 59437500000 3 = true :=
    take_step (n := 2) (t := 10) (b := 3592) rfl rfl ArealUCore.ArealUK.chunk_1795 s96
  have s94 : leavesOK ctxLitU 60620800000000 13 ((leaves.drop 3588).take 12) 59437500000 3 = true :=
    take_step (n := 2) (t := 12) (b := 3590) rfl rfl ArealUCore.ArealUK.chunk_1794 s95
  have s93 : leavesOK ctxLitU 59150000000 3 ((leaves.drop 3586).take 14) 59437500000 3 = true :=
    take_step (n := 2) (t := 14) (b := 3588) rfl rfl ArealUCore.ArealUK.chunk_1793 s94
  have s92 : leavesOK ctxLitU 118250000000 4 ((leaves.drop 3584).take 16) 59437500000 3 = true :=
    take_step (n := 2) (t := 16) (b := 3586) rfl rfl ArealUCore.ArealUK.chunk_1792 s93
  have s91 : leavesOK ctxLitU 236450000000 5 ((leaves.drop 3582).take 18) 59437500000 3 = true :=
    take_step (n := 2) (t := 18) (b := 3584) rfl rfl ArealUCore.ArealUK.chunk_1791 s92
  have s90 : leavesOK ctxLitU 236400000000 5 ((leaves.drop 3580).take 20) 59437500000 3 = true :=
    take_step (n := 2) (t := 20) (b := 3582) rfl rfl ArealUCore.ArealUK.chunk_1790 s91
  have s89 : leavesOK ctxLitU 118150000000 4 ((leaves.drop 3578).take 22) 59437500000 3 = true :=
    take_step (n := 2) (t := 22) (b := 3580) rfl rfl ArealUCore.ArealUK.chunk_1789 s90
  have s88 : leavesOK ctxLitU 59025000000 3 ((leaves.drop 3576).take 24) 59437500000 3 = true :=
    take_step (n := 2) (t := 24) (b := 3578) rfl rfl ArealUCore.ArealUK.chunk_1788 s89
  have s87 : leavesOK ctxLitU 29487500000 2 ((leaves.drop 3574).take 26) 59437500000 3 = true :=
    take_step (n := 2) (t := 26) (b := 3576) rfl rfl ArealUCore.ArealUK.chunk_1787 s88
  have s86 : leavesOK ctxLitU 29462500000 2 ((leaves.drop 3572).take 28) 59437500000 3 = true :=
    take_step (n := 2) (t := 28) (b := 3574) rfl rfl ArealUCore.ArealUK.chunk_1786 s87
  have s85 : leavesOK ctxLitU 58900000000 3 ((leaves.drop 3570).take 30) 59437500000 3 = true :=
    take_step (n := 2) (t := 30) (b := 3572) rfl rfl ArealUCore.ArealUK.chunk_1785 s86
  have s84 : leavesOK ctxLitU 117775000000 4 ((leaves.drop 3568).take 32) 59437500000 3 = true :=
    take_step (n := 2) (t := 32) (b := 3570) rfl rfl ArealUCore.ArealUK.chunk_1784 s85
  have s83 : leavesOK ctxLitU 117750000000 4 ((leaves.drop 3566).take 34) 59437500000 3 = true :=
    take_step (n := 2) (t := 34) (b := 3568) rfl rfl ArealUCore.ArealUK.chunk_1783 s84
  have s82 : leavesOK ctxLitU 117725000000 4 ((leaves.drop 3564).take 36) 59437500000 3 = true :=
    take_step (n := 2) (t := 36) (b := 3566) rfl rfl ArealUCore.ArealUK.chunk_1782 s83
  have s81 : leavesOK ctxLitU 117700000000 4 ((leaves.drop 3562).take 38) 59437500000 3 = true :=
    take_step (n := 2) (t := 38) (b := 3564) rfl rfl ArealUCore.ArealUK.chunk_1781 s82
  have s80 : leavesOK ctxLitU 58825000000 3 ((leaves.drop 3560).take 40) 59437500000 3 = true :=
    take_step (n := 2) (t := 40) (b := 3562) rfl rfl ArealUCore.ArealUK.chunk_1780 s81
  have s79 : leavesOK ctxLitU 58800000000 3 ((leaves.drop 3558).take 42) 59437500000 3 = true :=
    take_step (n := 2) (t := 42) (b := 3560) rfl rfl ArealUCore.ArealUK.chunk_1779 s80
  have s78 : leavesOK ctxLitU 29387500000 2 ((leaves.drop 3556).take 44) 59437500000 3 = true :=
    take_step (n := 2) (t := 44) (b := 3558) rfl rfl ArealUCore.ArealUK.chunk_1778 s79
  have s77 : leavesOK ctxLitU 29375000000 2 ((leaves.drop 3554).take 46) 59437500000 3 = true :=
    take_step (n := 2) (t := 46) (b := 3556) rfl rfl ArealUCore.ArealUK.chunk_1777 s78
  have s76 : leavesOK ctxLitU 58731250000 3 ((leaves.drop 3552).take 48) 59437500000 3 = true :=
    take_step (n := 2) (t := 48) (b := 3554) rfl rfl ArealUCore.ArealUK.chunk_1776 s77
  have s75 : leavesOK ctxLitU 117450000000 4 ((leaves.drop 3550).take 50) 59437500000 3 = true :=
    take_step (n := 2) (t := 50) (b := 3552) rfl rfl ArealUCore.ArealUK.chunk_1775 s76
  have s74 : leavesOK ctxLitU 58712500000 3 ((leaves.drop 3548).take 52) 59437500000 3 = true :=
    take_step (n := 2) (t := 52) (b := 3550) rfl rfl ArealUCore.ArealUK.chunk_1774 s75
  have s73 : leavesOK ctxLitU 58700000000 3 ((leaves.drop 3546).take 54) 59437500000 3 = true :=
    take_step (n := 2) (t := 54) (b := 3548) rfl rfl ArealUCore.ArealUK.chunk_1773 s74
  have s72 : leavesOK ctxLitU 29337500000 2 ((leaves.drop 3544).take 56) 59437500000 3 = true :=
    take_step (n := 2) (t := 56) (b := 3546) rfl rfl ArealUCore.ArealUK.chunk_1772 s73
  have s71 : leavesOK ctxLitU 30026350365496 12 ((leaves.drop 3542).take 58) 59437500000 3 = true :=
    take_step (n := 2) (t := 58) (b := 3544) rfl rfl ArealUCore.ArealUK.chunk_1771 s72
  have s70 : leavesOK ctxLitU 60029550365493 13 ((leaves.drop 3540).take 60) 59437500000 3 = true :=
    take_step (n := 2) (t := 60) (b := 3542) rfl rfl ArealUCore.ArealUK.chunk_1770 s71
  have s69 : leavesOK ctxLitU 120012800000000 14 ((leaves.drop 3538).take 62) 59437500000 3 = true :=
    take_step (n := 2) (t := 62) (b := 3540) rfl rfl ArealUCore.ArealUK.chunk_1769 s70
  have s68 : leavesOK ctxLitU 117187500000 4 ((leaves.drop 3536).take 64) 59437500000 3 = true :=
    take_step (n := 2) (t := 64) (b := 3538) rfl rfl ArealUCore.ArealUK.chunk_1768 s69
  have s67 : leavesOK ctxLitU 117168750000 4 ((leaves.drop 3534).take 66) 59437500000 3 = true :=
    take_step (n := 2) (t := 66) (b := 3536) rfl rfl ArealUCore.ArealUK.chunk_1767 s68
  have s66 : leavesOK ctxLitU 117156250000 4 ((leaves.drop 3532).take 68) 59437500000 3 = true :=
    take_step (n := 2) (t := 68) (b := 3534) rfl rfl ArealUCore.ArealUK.chunk_1766 s67
  have s65 : leavesOK ctxLitU 29281250000 2 ((leaves.drop 3530).take 70) 59437500000 3 = true :=
    take_step (n := 2) (t := 70) (b := 3532) rfl rfl ArealUCore.ArealUK.chunk_1765 s66
  have s64 : leavesOK ctxLitU 29268750000 2 ((leaves.drop 3528).take 72) 59437500000 3 = true :=
    take_step (n := 2) (t := 72) (b := 3530) rfl rfl ArealUCore.ArealUK.chunk_1764 s65
  have s63 : leavesOK ctxLitU 58525000000 3 ((leaves.drop 3526).take 74) 59437500000 3 = true :=
    take_step (n := 2) (t := 74) (b := 3528) rfl rfl ArealUCore.ArealUK.chunk_1763 s64
  have s62 : leavesOK ctxLitU 234081250000 5 ((leaves.drop 3524).take 76) 59437500000 3 = true :=
    take_step (n := 2) (t := 76) (b := 3526) rfl rfl ArealUCore.ArealUK.chunk_1762 s63
  have s61 : leavesOK ctxLitU 117031250000 4 ((leaves.drop 3522).take 78) 59437500000 3 = true :=
    take_step (n := 2) (t := 78) (b := 3524) rfl rfl ArealUCore.ArealUK.chunk_1761 s62
  have s60 : leavesOK ctxLitU 58506250000 3 ((leaves.drop 3520).take 80) 59437500000 3 = true :=
    take_step (n := 2) (t := 80) (b := 3522) rfl rfl ArealUCore.ArealUK.chunk_1760 s61
  have s59 : leavesOK ctxLitU 117000000000 4 ((leaves.drop 3518).take 82) 59437500000 3 = true :=
    take_step (n := 2) (t := 82) (b := 3520) rfl rfl ArealUCore.ArealUK.chunk_1759 s60
  have s58 : leavesOK ctxLitU 29237500000 2 ((leaves.drop 3516).take 84) 59437500000 3 = true :=
    take_step (n := 2) (t := 84) (b := 3518) rfl rfl ArealUCore.ArealUK.chunk_1758 s59
  have s57 : leavesOK ctxLitU 7300000000 0 ((leaves.drop 3514).take 86) 59437500000 3 = true :=
    take_step (n := 2) (t := 86) (b := 3516) rfl rfl ArealUCore.ArealUK.chunk_1757 s58
  have s56 : leavesOK ctxLitU 7287500000 0 ((leaves.drop 3512).take 88) 59437500000 3 = true :=
    take_step (n := 2) (t := 88) (b := 3514) rfl rfl ArealUCore.ArealUK.chunk_1756 s57
  have s55 : leavesOK ctxLitU 29842124568693 12 ((leaves.drop 3510).take 90) 59437500000 3 = true :=
    take_step (n := 2) (t := 90) (b := 3512) rfl rfl ArealUCore.ArealUK.chunk_1755 s56
  have s54 : leavesOK ctxLitU 29813926550812 12 ((leaves.drop 3508).take 92) 59437500000 3 = true :=
    take_step (n := 2) (t := 92) (b := 3510) rfl rfl ArealUCore.ArealUK.chunk_1754 s55
  have s53 : leavesOK ctxLitU 29798400000000 12 ((leaves.drop 3506).take 94) 59437500000 3 = true :=
    take_step (n := 2) (t := 94) (b := 3508) rfl rfl ArealUCore.ArealUK.chunk_1753 s54
  have s52 : leavesOK ctxLitU 7262500000 0 ((leaves.drop 3504).take 96) 59437500000 3 = true :=
    take_step (n := 2) (t := 96) (b := 3506) rfl rfl ArealUCore.ArealUK.chunk_1752 s53
  have s51 : leavesOK ctxLitU 14506250000 1 ((leaves.drop 3502).take 98) 59437500000 3 = true :=
    take_step (n := 2) (t := 98) (b := 3504) rfl rfl ArealUCore.ArealUK.chunk_1751 s52
  have s50 : leavesOK ctxLitU 29000000000 2 ((leaves.drop 3500).take 100) 59437500000 3 = true :=
    take_step (n := 2) (t := 100) (b := 3502) rfl rfl ArealUCore.ArealUK.chunk_1750 s51
  have s49 : leavesOK ctxLitU 57987500000 3 ((leaves.drop 3498).take 102) 59437500000 3 = true :=
    take_step (n := 2) (t := 102) (b := 3500) rfl rfl ArealUCore.ArealUK.chunk_1749 s50
  have s48 : leavesOK ctxLitU 57975000000 3 ((leaves.drop 3496).take 104) 59437500000 3 = true :=
    take_step (n := 2) (t := 104) (b := 3498) rfl rfl ArealUCore.ArealUK.chunk_1748 s49
  have s47 : leavesOK ctxLitU 115937500000 4 ((leaves.drop 3494).take 106) 59437500000 3 = true :=
    take_step (n := 2) (t := 106) (b := 3496) rfl rfl ArealUCore.ArealUK.chunk_1747 s48
  have s46 : leavesOK ctxLitU 115925000000 4 ((leaves.drop 3492).take 108) 59437500000 3 = true :=
    take_step (n := 2) (t := 108) (b := 3494) rfl rfl ArealUCore.ArealUK.chunk_1746 s47
  have s45 : leavesOK ctxLitU 57950000000 3 ((leaves.drop 3490).take 110) 59437500000 3 = true :=
    take_step (n := 2) (t := 110) (b := 3492) rfl rfl ArealUCore.ArealUK.chunk_1745 s46
  have s44 : leavesOK ctxLitU 28962500000 2 ((leaves.drop 3488).take 112) 59437500000 3 = true :=
    take_step (n := 2) (t := 112) (b := 3490) rfl rfl ArealUCore.ArealUK.chunk_1744 s45
  have s43 : leavesOK ctxLitU 28950000000 2 ((leaves.drop 3486).take 114) 59437500000 3 = true :=
    take_step (n := 2) (t := 114) (b := 3488) rfl rfl ArealUCore.ArealUK.chunk_1743 s44
  have s42 : leavesOK ctxLitU 57881250000 3 ((leaves.drop 3484).take 116) 59437500000 3 = true :=
    take_step (n := 2) (t := 116) (b := 3486) rfl rfl ArealUCore.ArealUK.chunk_1742 s43
  have s41 : leavesOK ctxLitU 57868750000 3 ((leaves.drop 3482).take 118) 59437500000 3 = true :=
    take_step (n := 2) (t := 118) (b := 3484) rfl rfl ArealUCore.ArealUK.chunk_1741 s42
  have s40 : leavesOK ctxLitU 57856250000 3 ((leaves.drop 3480).take 120) 59437500000 3 = true :=
    take_step (n := 2) (t := 120) (b := 3482) rfl rfl ArealUCore.ArealUK.chunk_1740 s41
  have s39 : leavesOK ctxLitU 57843750000 3 ((leaves.drop 3478).take 122) 59437500000 3 = true :=
    take_step (n := 2) (t := 122) (b := 3480) rfl rfl ArealUCore.ArealUK.chunk_1739 s40
  have s38 : leavesOK ctxLitU 57831250000 3 ((leaves.drop 3476).take 124) 59437500000 3 = true :=
    take_step (n := 2) (t := 124) (b := 3478) rfl rfl ArealUCore.ArealUK.chunk_1738 s39
  have s37 : leavesOK ctxLitU 28906250000 2 ((leaves.drop 3474).take 126) 59437500000 3 = true :=
    take_step (n := 2) (t := 126) (b := 3476) rfl rfl ArealUCore.ArealUK.chunk_1737 s38
  have s36 : leavesOK ctxLitU 57787500000 3 ((leaves.drop 3472).take 128) 59437500000 3 = true :=
    take_step (n := 2) (t := 128) (b := 3474) rfl rfl ArealUCore.ArealUK.chunk_1736 s37
  have s35 : leavesOK ctxLitU 115537500000 4 ((leaves.drop 3470).take 130) 59437500000 3 = true :=
    take_step (n := 2) (t := 130) (b := 3472) rfl rfl ArealUCore.ArealUK.chunk_1735 s36
  have s34 : leavesOK ctxLitU 115512500000 4 ((leaves.drop 3468).take 132) 59437500000 3 = true :=
    take_step (n := 2) (t := 132) (b := 3470) rfl rfl ArealUCore.ArealUK.chunk_1734 s35
  have s33 : leavesOK ctxLitU 115487500000 4 ((leaves.drop 3466).take 134) 59437500000 3 = true :=
    take_step (n := 2) (t := 134) (b := 3468) rfl rfl ArealUCore.ArealUK.chunk_1733 s34
  have s32 : leavesOK ctxLitU 115462500000 4 ((leaves.drop 3464).take 136) 59437500000 3 = true :=
    take_step (n := 2) (t := 136) (b := 3466) rfl rfl ArealUCore.ArealUK.chunk_1732 s33
  have s31 : leavesOK ctxLitU 115437500000 4 ((leaves.drop 3462).take 138) 59437500000 3 = true :=
    take_step (n := 2) (t := 138) (b := 3464) rfl rfl ArealUCore.ArealUK.chunk_1731 s32
  have s30 : leavesOK ctxLitU 57700000000 3 ((leaves.drop 3460).take 140) 59437500000 3 = true :=
    take_step (n := 2) (t := 140) (b := 3462) rfl rfl ArealUCore.ArealUK.chunk_1730 s31
  have s29 : leavesOK ctxLitU 57675000000 3 ((leaves.drop 3458).take 142) 59437500000 3 = true :=
    take_step (n := 2) (t := 142) (b := 3460) rfl rfl ArealUCore.ArealUK.chunk_1729 s30
  have s28 : leavesOK ctxLitU 115325000000 4 ((leaves.drop 3456).take 144) 59437500000 3 = true :=
    take_step (n := 2) (t := 144) (b := 3458) rfl rfl ArealUCore.ArealUK.chunk_1728 s29
  have s27 : leavesOK ctxLitU 115300000000 4 ((leaves.drop 3454).take 146) 59437500000 3 = true :=
    take_step (n := 2) (t := 146) (b := 3456) rfl rfl ArealUCore.ArealUK.chunk_1727 s28
  have s26 : leavesOK ctxLitU 115275000000 4 ((leaves.drop 3452).take 148) 59437500000 3 = true :=
    take_step (n := 2) (t := 148) (b := 3454) rfl rfl ArealUCore.ArealUK.chunk_1726 s27
  have s25 : leavesOK ctxLitU 115250000000 4 ((leaves.drop 3450).take 150) 59437500000 3 = true :=
    take_step (n := 2) (t := 150) (b := 3452) rfl rfl ArealUCore.ArealUK.chunk_1725 s26
  have s24 : leavesOK ctxLitU 115225000000 4 ((leaves.drop 3448).take 152) 59437500000 3 = true :=
    take_step (n := 2) (t := 152) (b := 3450) rfl rfl ArealUCore.ArealUK.chunk_1724 s25
  have s23 : leavesOK ctxLitU 115200000000 4 ((leaves.drop 3446).take 154) 59437500000 3 = true :=
    take_step (n := 2) (t := 154) (b := 3448) rfl rfl ArealUCore.ArealUK.chunk_1723 s24
  have s22 : leavesOK ctxLitU 115175000000 4 ((leaves.drop 3444).take 156) 59437500000 3 = true :=
    take_step (n := 2) (t := 156) (b := 3446) rfl rfl ArealUCore.ArealUK.chunk_1722 s23
  have s21 : leavesOK ctxLitU 115150000000 4 ((leaves.drop 3442).take 158) 59437500000 3 = true :=
    take_step (n := 2) (t := 158) (b := 3444) rfl rfl ArealUCore.ArealUK.chunk_1721 s22
  have s20 : leavesOK ctxLitU 115125000000 4 ((leaves.drop 3440).take 160) 59437500000 3 = true :=
    take_step (n := 2) (t := 160) (b := 3442) rfl rfl ArealUCore.ArealUK.chunk_1720 s21
  have s19 : leavesOK ctxLitU 115100000000 4 ((leaves.drop 3438).take 162) 59437500000 3 = true :=
    take_step (n := 2) (t := 162) (b := 3440) rfl rfl ArealUCore.ArealUK.chunk_1719 s20
  have s18 : leavesOK ctxLitU 115075000000 4 ((leaves.drop 3436).take 164) 59437500000 3 = true :=
    take_step (n := 2) (t := 164) (b := 3438) rfl rfl ArealUCore.ArealUK.chunk_1718 s19
  have s17 : leavesOK ctxLitU 115050000000 4 ((leaves.drop 3434).take 166) 59437500000 3 = true :=
    take_step (n := 2) (t := 166) (b := 3436) rfl rfl ArealUCore.ArealUK.chunk_1717 s18
  have s16 : leavesOK ctxLitU 115025000000 4 ((leaves.drop 3432).take 168) 59437500000 3 = true :=
    take_step (n := 2) (t := 168) (b := 3434) rfl rfl ArealUCore.ArealUK.chunk_1716 s17
  have s15 : leavesOK ctxLitU 115000000000 4 ((leaves.drop 3430).take 170) 59437500000 3 = true :=
    take_step (n := 2) (t := 170) (b := 3432) rfl rfl ArealUCore.ArealUK.chunk_1715 s16
  have s14 : leavesOK ctxLitU 114975000000 4 ((leaves.drop 3428).take 172) 59437500000 3 = true :=
    take_step (n := 2) (t := 172) (b := 3430) rfl rfl ArealUCore.ArealUK.chunk_1714 s15
  have s13 : leavesOK ctxLitU 114950000000 4 ((leaves.drop 3426).take 174) 59437500000 3 = true :=
    take_step (n := 2) (t := 174) (b := 3428) rfl rfl ArealUCore.ArealUK.chunk_1713 s14
  have s12 : leavesOK ctxLitU 114925000000 4 ((leaves.drop 3424).take 176) 59437500000 3 = true :=
    take_step (n := 2) (t := 176) (b := 3426) rfl rfl ArealUCore.ArealUK.chunk_1712 s13
  have s11 : leavesOK ctxLitU 114900000000 4 ((leaves.drop 3422).take 178) 59437500000 3 = true :=
    take_step (n := 2) (t := 178) (b := 3424) rfl rfl ArealUCore.ArealUK.chunk_1711 s12
  have s10 : leavesOK ctxLitU 114875000000 4 ((leaves.drop 3420).take 180) 59437500000 3 = true :=
    take_step (n := 2) (t := 180) (b := 3422) rfl rfl ArealUCore.ArealUK.chunk_1710 s11
  have s9 : leavesOK ctxLitU 114850000000 4 ((leaves.drop 3418).take 182) 59437500000 3 = true :=
    take_step (n := 2) (t := 182) (b := 3420) rfl rfl ArealUCore.ArealUK.chunk_1709 s10
  have s8 : leavesOK ctxLitU 114825000000 4 ((leaves.drop 3416).take 184) 59437500000 3 = true :=
    take_step (n := 2) (t := 184) (b := 3418) rfl rfl ArealUCore.ArealUK.chunk_1708 s9
  have s7 : leavesOK ctxLitU 114800000000 4 ((leaves.drop 3414).take 186) 59437500000 3 = true :=
    take_step (n := 2) (t := 186) (b := 3416) rfl rfl ArealUCore.ArealUK.chunk_1707 s8
  have s6 : leavesOK ctxLitU 57387500000 3 ((leaves.drop 3412).take 188) 59437500000 3 = true :=
    take_step (n := 2) (t := 188) (b := 3414) rfl rfl ArealUCore.ArealUK.chunk_1706 s7
  have s5 : leavesOK ctxLitU 57375000000 3 ((leaves.drop 3410).take 190) 59437500000 3 = true :=
    take_step (n := 2) (t := 190) (b := 3412) rfl rfl ArealUCore.ArealUK.chunk_1705 s6
  have s4 : leavesOK ctxLitU 57362500000 3 ((leaves.drop 3408).take 192) 59437500000 3 = true :=
    take_step (n := 2) (t := 192) (b := 3410) rfl rfl ArealUCore.ArealUK.chunk_1704 s5
  have s3 : leavesOK ctxLitU 57350000000 3 ((leaves.drop 3406).take 194) 59437500000 3 = true :=
    take_step (n := 2) (t := 194) (b := 3408) rfl rfl ArealUCore.ArealUK.chunk_1703 s4
  have s2 : leavesOK ctxLitU 57337500000 3 ((leaves.drop 3404).take 196) 59437500000 3 = true :=
    take_step (n := 2) (t := 196) (b := 3406) rfl rfl ArealUCore.ArealUK.chunk_1702 s3
  have s1 : leavesOK ctxLitU 57325000000 3 ((leaves.drop 3402).take 198) 59437500000 3 = true :=
    take_step (n := 2) (t := 198) (b := 3404) rfl rfl ArealUCore.ArealUK.chunk_1701 s2
  have s0 : leavesOK ctxLitU 57312500000 3 ((leaves.drop 3400).take 200) 59437500000 3 = true :=
    take_step (n := 2) (t := 200) (b := 3402) rfl rfl ArealUCore.ArealUK.chunk_1700 s1
  exact s0

end Areal.UCert
