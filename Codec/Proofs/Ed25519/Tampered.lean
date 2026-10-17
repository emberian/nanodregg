import Codec.Proofs.Ed25519Stage

/-!
# The plant: TEST 2's signature over a different message is refused, kernel-checked in stages

Each theorem is stated as before (verify / publicKey / sign over the RFC bytes); the proof goes
through literal intermediate points, so each kernel check holds one chunk of the ladder
(Codec.Proofs.Ed25519Stage). The literals are checked, not trusted: every `*_eq` below is a
`decide +kernel` of the real definitions landing exactly on them.
-/

namespace Nanodregg.Codec.Ed25519

private def pk : ByteArray := ⟨#[0x3d, 0x40, 0x17, 0xc3, 0xe8, 0x43, 0x89, 0x5a, 0x92, 0xb7, 0x0a, 0xa7, 0x4d, 0x1b, 0x7e, 0xbc,
    0x9c, 0x98, 0x2c, 0xcf, 0x2e, 0xc4, 0x96, 0x8c, 0xc0, 0xcd, 0x55, 0xf1, 0x2a, 0xf4, 0x66, 0x0c]⟩

private def sig : ByteArray := ⟨#[0x92, 0xa0, 0x09, 0xa9, 0xf0, 0xd4, 0xca, 0xb8, 0x72, 0x0e, 0x82, 0x0b, 0x5f, 0x64, 0x25, 0x40,
    0xa2, 0xb2, 0x7b, 0x54, 0x16, 0x50, 0x3f, 0x8f, 0xb3, 0x76, 0x22, 0x23, 0xeb, 0xdb, 0x69, 0xda,
    0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e, 0x45, 0x8f, 0x36, 0x13, 0xd0, 0xf1, 0x1d, 0x8c,
    0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee, 0xb0, 0x0d, 0x29, 0x16, 0x12, 0xbb, 0x0c, 0x00]⟩

private def TTA : Point := ⟨⟨64897966, 12060565, 19784841, 16626984, 33691620, 25579090, 10433218, 17397776, 33928435, 30586016⟩, ⟨51855421, 5306928, 49433425, 7157845, 49412205, 19699868, 56760167, 28840338, 45028700, 3251152⟩, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨64811122, 31179785, 22760827, 17027091, 52627072, 22335646, 42089315, 23831890, 57198025, 5395586⟩⟩
private def TTR : Point := ⟨⟨65327809, 8108135, 60078557, 23466162, 1343, 26068926, 66492913, 22703596, 35411834, 5635533⟩, ⟨17408146, 11877418, 30299929, 16276496, 16815505, 8106658, 61344554, 14053863, 45232679, 23701359⟩, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨21738259, 33246780, 11854462, 16142389, 47816749, 22521344, 39566628, 15039412, 2660422, 19993837⟩⟩
private def TTS : Nat := 22493278956989295319831480986006851106061907369804654499116800046813764104
private def TTk : Nat := 4101351592509810072392520702210171768151752000121383322933946776802592306645
private def TTc1 : Point := ⟨⟨47688504, 23322439, 41757140, 22710190, 7220040, 6080622, 30603254, 19201115, 56247988, 28225832⟩, ⟨64110969, 1508869, 50155205, 6835703, 45039434, 20768361, 47238336, 1794707, 48319250, 30015090⟩, ⟨62748839, 25612691, 13787905, 11996677, 40931261, 8145543, 14426070, 8315834, 56280543, 4946853⟩, ⟨55673364, 1345727, 42564783, 16339695, 62144442, 31315236, 2610412, 14837695, 58562926, 5302365⟩⟩
private def TTc2 : Point := ⟨⟨33227178, 717304, 36402946, 18389593, 22323476, 31244247, 58056361, 21804065, 18254150, 31175091⟩, ⟨8365322, 28361238, 34005119, 18023646, 7952094, 15682163, 42523409, 1005491, 20729628, 7032104⟩, ⟨47164642, 3108024, 57379163, 14491567, 25942918, 25718962, 60601514, 13756274, 29222225, 3716879⟩, ⟨57358334, 15736634, 46366224, 24127946, 41071620, 14695641, 48377032, 579164, 61326175, 30302160⟩⟩
private def TTc3 : Point := ⟨⟨56495465, 28756030, 57201518, 5988579, 15811676, 9695694, 63463766, 13064665, 56098659, 18315079⟩, ⟨21510637, 12578848, 18375236, 24578570, 36178843, 22164084, 6469633, 25712476, 9459940, 5713639⟩, ⟨3199758, 9565083, 39330967, 22505885, 55734848, 8307751, 10854356, 30835162, 41808214, 22756374⟩, ⟨22890518, 14014837, 21209621, 6201631, 44304023, 26996505, 55434607, 6533111, 12554294, 20012828⟩⟩
private def TTc4 : Point := ⟨⟨28948868, 32863207, 602356, 8546422, 55492008, 4687745, 48878189, 17254989, 44455257, 10127247⟩, ⟨4292421, 29716512, 5466333, 19112633, 2771608, 14116616, 56352898, 19894544, 40990051, 1603245⟩, ⟨30401869, 19130876, 20431536, 6386165, 45881957, 7931969, 3107253, 22568330, 37260018, 10643141⟩, ⟨33711895, 26029531, 40914063, 19371751, 45865898, 22231012, 31005063, 12955850, 19644462, 1864138⟩⟩

private theorem TTA_eq : decodePoint pk 0 = some TTA := by decide +kernel
private theorem TTR_eq : decodePoint sig 0 = some TTR := by decide +kernel
private theorem TTS_eq : leNat sig 32 32 = TTS := by decide +kernel
private theorem TTk_eq : leNat (Sha512.hash (sig.extract 0 32 ++ pk ++ ⟨#[0x73]⟩)).val 0 64 % L = TTk := by
  decide +kernel
private theorem TTc1_eq :
    Point.ladder B TTA.neg (B.add TTA.neg) Point.zero (TTS >>> 192) (TTk >>> 192) 61 = TTc1 := by
  decide +kernel
private theorem TTc2_eq :
    Point.ladder B TTA.neg (B.add TTA.neg) TTc1 (TTS >>> 128) (TTk >>> 128) 64 = TTc2 := by
  decide +kernel
private theorem TTc3_eq :
    Point.ladder B TTA.neg (B.add TTA.neg) TTc2 (TTS >>> 64) (TTk >>> 64) 64 = TTc3 := by
  decide +kernel
private theorem TTc4_eq :
    Point.ladder B TTA.neg (B.add TTA.neg) TTc3 TTS TTk 64 = TTc4 := by
  decide +kernel

/-- The plant: TEST 2's signature does not sign 0x73. -/
theorem test2_tampered : verify pk ⟨#[0x73]⟩ sig = false := by
  rw [verify_eq (by decide) (by decide) (by rw [TTS_eq]; decide) TTA_eq TTR_eq, TTS_eq, TTk_eq,
    mul2_of_chunks (n := 61) rfl TTc1_eq TTc2_eq TTc3_eq TTc4_eq]
  decide +kernel

end Nanodregg.Codec.Ed25519
