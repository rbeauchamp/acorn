import Acorn.Handcrafted.Agent
import Acorn.Rng
import Acorn.Word
import AcornVerif.CurrentExplorer
import AcornVerif.CurrentTemporal
import AcornVerif.TemporalSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace AcornVerif.CurrentXoshiroPeriod
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentExplorer AcornVerif.CurrentTemporal AcornVerif.TemporalSupport

private def mask64 : Nat := (1 <<< 64) - 1
private def mask255 : Nat := (1 <<< 255) - 1
private def mask256 : Nat := (1 <<< 256) - 1

def stepNat (v : Nat) : Nat :=
  let s0 := v &&& mask64
  let s1 := (v >>> 64) &&& mask64
  let s2 := (v >>> 128) &&& mask64
  let s3 := (v >>> 192) &&& mask64
  let shifted := (s1 <<< 17) &&& mask64
  let s2a := s2 ^^^ s0
  let s3a := s3 ^^^ s1
  let s1b := s1 ^^^ s2a
  let s0b := s0 ^^^ s3a
  let s2b := s2a ^^^ shifted
  let s3b := ((s3a <<< 45) &&& mask64) ||| (s3a >>> 19)
  s0b ||| (s1b <<< 64) ||| (s2b <<< 128) ||| (s3b <<< 192)

def pLow : Nat :=
  0x3c03c3f3ecb1904b4edcf26259f850280002bcefd1a5e9d116f2bb0f0f001

def barrettQ0 : Nat :=
  0x8001e01cb799614c0995b0f93bc5b4f0d5094bf56eaf3b5bc9d4836cab7de244

private def repMask : Nat → Nat → Nat → Nat
  | acc, _, 0 => acc
  | acc, period, k + 1 => repMask (acc ||| (acc <<< period)) (2 * period) k

private def sLo (b k : Nat) : Nat := repMask ((1 <<< b) - 1) (32 * b) k
private def sHi (b k : Nat) : Nat := (sLo b k) <<< b
private def cLo (b k : Nat) : Nat := repMask ((1 <<< b) - 1) (32 * b) k
private def cHi (b k : Nat) : Nat := (cLo b k) <<< (16 * b)
private def lane0Mask : Nat := repMask 1 16 9

private def mSLo128 := sLo 128 0
private def mSHi128 := sHi 128 0
private def mSLo64 := sLo 64 1
private def mSHi64 := sHi 64 1
private def mSLo32 := sLo 32 2
private def mSHi32 := sHi 32 2
private def mSLo16 := sLo 16 3
private def mSHi16 := sHi 16 3
private def mSLo8 := sLo 8 4
private def mSHi8 := sHi 8 4
private def mSLo4 := sLo 4 5
private def mSHi4 := sHi 4 5
private def mSLo2 := sLo 2 6
private def mSHi2 := sHi 2 6
private def mSLo1 := sLo 1 7
private def mSHi1 := sHi 1 7

private def mCLo1 := cLo 1 8
private def mCHi1 := cHi 1 8
private def mCLo2 := cLo 2 7
private def mCHi2 := cHi 2 7
private def mCLo4 := cLo 4 6
private def mCHi4 := cHi 4 6
private def mCLo8 := cLo 8 5
private def mCHi8 := cHi 8 5
private def mCLo16 := cLo 16 4
private def mCHi16 := cHi 16 4
private def mCLo32 := cLo 32 3
private def mCHi32 := cHi 32 3
private def mCLo64 := cLo 64 2
private def mCHi64 := cHi 64 2
private def mCLo128 := cLo 128 1
private def mCHi128 := cHi 128 1
private def mCLo256 := cLo 256 0
private def mCHi256 := cHi 256 0

private def sStep (mLo mHi s x : Nat) : Nat := (x &&& mLo) ||| ((x &&& mHi) <<< s)
private def cStep (mLo mHi s x : Nat) : Nat := (x &&& mLo) ||| ((x &&& mHi) >>> s)

private def spread16 (x : Nat) : Nat :=
  sStep mSLo1 mSHi1 15 <| sStep mSLo2 mSHi2 30 <| sStep mSLo4 mSHi4 60 <|
    sStep mSLo8 mSHi8 120 <| sStep mSLo16 mSHi16 240 <| sStep mSLo32 mSHi32 480 <|
    sStep mSLo64 mSHi64 960 <| sStep mSLo128 mSHi128 1920 x

private def compress16 (y : Nat) : Nat :=
  cStep mCLo256 mCHi256 3840 <| cStep mCLo128 mCHi128 1920 <| cStep mCLo64 mCHi64 960 <|
    cStep mCLo32 mCHi32 480 <| cStep mCLo16 mCHi16 240 <| cStep mCLo8 mCHi8 120 <|
    cStep mCLo4 mCHi4 60 <| cStep mCLo2 mCHi2 30 <| cStep mCLo1 mCHi1 15 <| (y &&& lane0Mask)

def clMul (a b : Nat) : Nat := compress16 (spread16 a * spread16 b)

def polyMul (a b : Nat) : Nat :=
  let c := clMul a b
  let q := (clMul (c >>> 256) barrettQ0) >>> 255
  (c ^^^ clMul q pLow) &&& mask256

private def polyPowGo : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, e, acc =>
    if e == 0 || acc == 0 then acc
    else if a == 0 then 0
    else
      let acc1 := if e &&& 1 == 1 then polyMul acc a else acc
      polyPowGo fuel (polyMul a a) (e >>> 1) acc1

def polyPow (a e : Nat) : Nat := polyPowGo 257 a e 1

private def evalPolyGo : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, f, cur, acc =>
    let acc1 := if f &&& 1 == 1 then acc ^^^ cur else acc
    evalPolyGo n (f >>> 1) (stepNat cur) acc1

def evalPoly (f : Nat) : Nat := evalPolyGo 256 f 1 0

def iterStep : Nat → Nat → Nat
  | 0, v => v
  | n + 1, v => iterStep n (stepNat v)

private def invBasisList : List Nat := [
  0x0000000000000000000000000000000000000000000000000000000000000001,
  0xf2c9adf7af0df9f465ab73f77cd3a2ef3c25140c5c9c3038e1dedd95ca1747bb,
  0x0b460444ac625d79b203cd6b025af2f4ac2a3bb3949b9b88bb714d51dc513ff9,
  0x3551458e3890805b945c1b47157b3a5e69b3afa458ab4f609978da00617ff5df,
  0xdf47767c553f3001a1d225b497038b0a8296cd3a1e5e73c9d37648a6a077762c,
  0x919955f819cf734aae74a0c3528773bf594698cbe24c201bf75bb029e5370af6,
  0x4f360160b8ba7f5839a35309544b938097aa4026f3c3246637d527114e9e5c03,
  0x878e684570dd1a2fb420385235f699a998ad6fbb19907ff9f2e21b93d5c0bb00,
  0x0877ae21c02c2f0d8f023f169078d5ba155bf47e5d123c6966f8bfa66bbe07f2,
  0x8443be2e129ae113b575190e092eda0c4bb3d7964eac24622d80c1e9a8aa51f3,
  0xac86331b906f1879278675f2f91c33f2d73e6d9fcc56dc6d5524f5ae275f3594,
  0x8c7bd673189f29a00644c1bc411593687c063b2b45b0e0377787b22ce9a70db6,
  0x8b48e6dc3ee323f718ef9aeba1ebda63ee156c10a348d0b758e9ccb2c611da0f,
  0x3c0983725f6e0a82965f304d65de789c2c8f887cb776dbdb9298aadf12472bf2,
  0x0ce2bb4c57d9bd28a735e07cef04e43c8fa63333b1f5e002019a9a8e232b213e,
  0x48f60e0a500cd7ea18f2b39ee60290def1e935bdc1e2ffeb161296e849eab201,
  0x9214069e88fd4d32d92800681171d7541cda6a0b12e646193d5c2497d0a5f6af,
  0xf765117ab7bdca5917e70b6aebd99d35693efad2fb24dec4f9ef5c4b4297aafc,
  0xec48e053e19f460ef691f5491ccc7ca8d85501b197b93a9ad5ffa09be83e4edb,
  0x81478d3e7da97a2d9c785136f3f04442aef9a71b507f20b6e47cca56aa7a9e45,
  0x96d538ee43b0728a2a28e01c5b87169df7aebae792938ce632a5976409e10449,
  0x052e56790d730b665e764f0de28c69d6382056c0236744ff6502769bd863b017,
  0x0059775805a2f1a9e797c407f95007f2e605a4f1a6154310e9218c028ab2d984,
  0x55759818f8a22dc5c56d946938bbef5c0ce147d9cb4de6d20c06b110e316b421,
  0xb7e0cf5459a9150148908641c2e7c7d9f537dc2a55eb94c88e9c9f82d5c01a0b,
  0x3a74ea63bdaf892e80beaa8c5383564fa427c620cf849a7398b05dc2f0cc9f5a,
  0x1f7e55eca1bd520677be006d8e34b9665fb54310b7773899b6e4e17452361fb6,
  0xe23a606b789ae0b17e3198ec56ed9af4f993df6acf0de2a732c2827db3c507b6,
  0xfac451a8560880a12c127103ebaee67070e91848508324138cf300c012cbfd02,
  0x845ed8a3a86fa7347123109ca8d5472bc280f77498b87365a1a9c29fa49d9243,
  0xde2e2570cac9424f5150daa66b71f2e901b7dd57563489b91f583c2ca02be3d3,
  0xe95777bc2e70a59eb57fbbfd9f6292bbd2792aa0670378e213dedbbd61139002,
  0x5691044a4901cbd416aa594bfce5e38517602b0c5be0e539ed60f057a9c9bdf6,
  0x1f62a7cd1b67f0a4cb1051648c6d9b00c94489d5c39ccfd026a76adba409a306,
  0x5bf0110a1b2e33841ac5015891119a4b65fb0b5dc079a7740f6392847d2ce324,
  0xa9cefbb2398fde751a075e9c8d033999d6ab7cb1cf3dbf4733eaf5f8a952c432,
  0x8197a7371801283f05095cfacbdbec99116e83b0893f4bb9c585577028ee41a9,
  0xc3cfb69a0840156fc1ad4d65fb58a271fe2d5f79346d7c065a6b9b9c74f00926,
  0x442fa7f8fec3fde23f315234282ac158ae5cd073d8054526ee6c5139d5e7ff7d,
  0xc5ccfa104c4ea917c8c3bc7bdde4f53bd803da661447c47bef897c5fca45ede6,
  0x3541748facd1b46868bed551f2ab30fdeeecf5b3515237de78b96d75f6344bde,
  0xd90a7d792d282235eff7a1722f49a007ed616b462ebb003479403bb048fd8d83,
  0x934c81c6d9b632a9f3dd52ad03800717900ca6c845043fbcec1de38eb7216bb6,
  0x1ffb87dd592a5db160f711ad7a70cbeb3191b42b49c4613eb55dad8aaa6c7531,
  0xdf151fadca38f28b46d1e95bbd70287e44b7c6dd26a4d1c230ad372015834ff9,
  0x784d601d889e9508ab04072506a8b174f5278c34e9430c94aa7b06e0af15bc30,
  0xece66530c6962977860b3d87e954b8dcf4a98d21e525e3dc53b9f0dbcbb0f508,
  0x110d6660856a26f51ab823bd6fd53955fd362620f6c3b74d20c0f82e2faf52c9,
  0x13731e8f7e052045c917769561b48b6cc92c593c3dcbf9d93d90bd5c686b1033,
  0xe13618d737a989ea1ee7a32ea1e8b4d21ce38f67eeecc1f8a114a8ea5551277f,
  0xe3b5d2841d30ddf22e6c3ccdce4b63452df24aac7dc3004ef9e7424484c45807,
  0xb84cb22cfc89e93a2ee3286f22eba23fd993cfb863226cf8ce5a2745bb4be98b,
  0xdd1605839d4476f956b883a3c7ff63a33cf08321c5410af1b4fc494cc05e5350,
  0xc1a8e347ef8a8d9eb3a06220e9608f49990082b39b08383d853d019d7000d8d4,
  0xcbd1a53b7d01d3f3d5e6b80f7790c995e0bb7574018ea3980727bfa7a6933345,
  0x2e430dcc18c87e7b62625db74347e6bda17fd27d64485c93bb902e31f17dfba3,
  0xd356e8ce367ae60a4e10de3b84f7807cb82d58f851fe8a173edb643cfbf8051d,
  0x1318159d212269000ab2524aa69d2134db16949c8b524d144e31b504ac97fe56,
  0x4eac4963c14804e3302b6779d28ac9ecba2d02f1997e144a3be429067fad8bb7,
  0x26fea1baeb2a4023493f5e18c459a0f35cb2afa2760388d7bd7bca9144bf07f5,
  0xd20eda578f7681dc663b60417732c050cc72a09bfd7b2b94c974f582f5d45807,
  0xe9286a960c0eb016907539bbe66597ec7ae8656f4bea496075dac159d9a2818d,
  0x884c7d752f75136f2b49a9de29a5c44ef244495bffad8a8584b97f12063c4901,
  0xb2dea88091ac86cdf10ab9187ad2975c5734fdd4d83f34abef97db4e9a9ccb91,
  0x8001e01e1f9f658c825a76e79312cfc281400015e77e8d2f4e88b795d8787802,
  0x1cf5ad36a93ca1877f6dc53df2f9c4ee6598a220bef5ef1c60cb0d5f19ada4aa,
  0x932eeab5116af1c33f5c0a84168a53518f016aab040477fa65d28b9e8ef2980e,
  0xf00bc9c572f6251660cc4dca3359265166fe888f7a7db45e30c56e952a386951,
  0xd12e97fabfdf331a97f9b47c43a34c1546e6fcc2fd6ec429d246da35a025a74f,
  0x6bfdc130004794290f67fc282a68c1241cae7dd9fb434a64880bd76c88056096,
  0x39f6e26f32b6a490edcd797191a02103e5c1a04b791957d03ac86a3fe20bee07,
  0x4cd8249466ea7251b6e481425733e002ff8c68807115da5181a455c5f191db81,
  0x14d48b53604e499dd98561a668cdc1a9201a12c394ad66e67e8d209fe2a30c1d,
  0xcaa483690cd91c3b36be25b3a3fd8959317e44d9938dcd849e583b99ed89031e,
  0x0f4cbf86d7d777d7d87b3cd3a893e199c763eddbb07bccb29dcafea0ede101e3,
  0x5ec987e3824f0c890b1f0e69848470e1c48f6be8e744aa2bc9ddd264176d6db6,
  0xd3379ef4421678803b46638a261509b1a8e06e173eb65e44ce3ea78287a3d118,
  0x6617c75d916b10446791f8bc7953cd764f58d4c73556da5aec7d00d1adadc21d,
  0x1fb42b3e845fa4c51df130c7a98bba67589f7ffebb11300503f8785b57c3d2e3,
  0x3596fb0f9780a1adbfc648152c16a6101a66f1b0844a0d0ce9a4d1316f584502,
  0xed202e5075259269582a9bcc9f6c1545b419e12d853c384f378f83da21919e08,
  0x957b6a740b9bba87a0897eaf847a6b75646288e74526c8b51238799894947087,
  0x2eb790ac1350818f10858b1e02c997425f408385cd2d7f09129949c44ceb32da,
  0xc22efcc1e527e7d8702211de2b2ffae3894f9d8521424647695e29386940fba9,
  0xe6c2cd89861972c4c7ab2b1e2ffaf632974a2882c5ed48ceaf803dc47fba02b7,
  0x88ca67d083c0f6f3118dcf7aa74c2885ed1086f5b003a6ae360d61ef848ec025,
  0x009e551c09949b873ce46a0c0e080c1cbf099b9b9f2027a9a6d3de04503cdfca,
  0x00501c23928a28e5ea3794017e38e6d49ef22c4a9443b3e250868d3c6fde4a52,
  0xb433d920bf270e17b387d48bd18b3c189334567fa8a1748489eea87aa9e8b112,
  0x69d3a1f6a588d6ca4122005e8ec707b89a5c6f51f8cb79defd38956499ff7119,
  0x3143812f13a40d0fd4a300eddb732e7f90b027a93555ed7fb6bbb2528d7730b7,
  0xb56a30df72467a2347cf1061a08867168d6e514b37602e4361f52aee0e987cb6,
  0x88e94bb8b82b8a0bca99374904af205ddb26bc9f47bac070428eeecb9c02f484,
  0xca90fd34a44933675c39325fb0f77d85e781956d54af4808401ebccef3fd65a6,
  0x5349787bd0578b2c8ce74337566c4ce10074543b2ef0c0df6285bef178cabe4e,
  0xa606949a74e7d2eb34f447cad751f3af4f4ec03b337a57ebb343b58fc25e1804,
  0x866a8ab1b683724226019e3207b936c8a570439e9a31b8ef2c7198848777a517,
  0x31741c7cbb7c191bf3a88a7b5eedfb81f62b574166f7f8485e1d60da9a17978f,
  0x9a182a913bcb7eca38e8821d6aabf9b3790b931560cf9d521976ec4ac4cfb7da,
  0x07794a8150e698c9bdb9ffb87aa2707a44834710b718bb736331fe26b6fc1a7c,
  0xc3e6bdd79ca36af40e788ca0476d7f3929aa46877f62a5deba51dde62d232b87,
  0xe67b76452b9eeb716738d1b62d388a5e01cc11653c115c5104f395dd6368e6de,
  0x2a497c139d7960b9e3a07b95d7522ddf8ad7c8cbbb76a5f1e5663d7a99447944,
  0xe97c49148184cdbd71524b05731e0f6f5e8659d4ec517094b5c729bbc159dd3e,
  0x702253588fcbb2e4e522c00b1c03f9852aaf91bf0a0d7453cd2e6c511772b253,
  0x5e93e46cec65fbe4aefa0975fc00c04bafb2631163a817031db9b206dd0d55c6,
  0x6f3c8352e089b71e1ae0e1c3a0e59221ea9f1edf66777af9332459f1852292b6,
  0xb00b2c4a015ef036f3cfdd6bdacb3de17aabb256d0147fcd7e9d3a45d996a8fa,
  0x51a290af51cc32c6a825bd32116f148428f46eeaf7985c14aa952d6e494fb00f,
  0xccbc7035d5726095038a0dd88e053a5390dcde73a6279f6301cb8eb109a1a678,
  0xafbc38c5d1598d4dcba708030026b2529187dcf8f6242c0813be76f1c2496095,
  0xaa9d9fef57fe3b1c3a762043fb5221c385b75f44719838139f693bde90f174f6,
  0xaf5e52475c97b525f4ff2087e0a19cad778e9ef3820c8271ab6193833c9bd07f,
  0x32f51de7d42679b4b4520ce2a612638ab476d942032c747cc13add1fe8825540,
  0x36b36c6814587b88cd00fcd5ce84276f4eddb030ece417cb5ca4fd152362140c,
  0xacbd1d6da7f6887ccc595fc16195c527dc2e7892de5678fc28008597c3baafd2,
  0xd4a4c9facb141d970299ab594a24e912e51947f8a6df8ac52e97d91450637f09,
  0xe386771017ee96eb3a24189e8054c6b2fc0144153569763b55f5ecdfe8f12dc3,
  0x7249b8c96422e08bc7d0b731e1dea7a6b2eb506c2a59818dde457822f6e77729,
  0xcba67d60226ba647f7afe352b43ef1e713004dd19dca1a41e460fceec23d7297,
  0x4f0485d9576911843dc748427ea39080af8c1db2a281c6543142a2d9e28480b5,
  0x2fbc21f4d2d5e680103d8db01e74d2f3dba66377530dbca2bb7bb08b0f640387,
  0x3a0f56687dab6e3b7a190ba8df4238eda80c848e193daf9e24b2f11a18f5aab5,
  0xde83f3b6bc5ec5dbb4bb65da798d5e5d967c0880307858ebeac2c7fff359f410,
  0x4d18f9a6f9f7edc37985eb8ae0cbb0ce7d1c11442dc8559225ca497af9ca140c,
  0x26c6c0453ebb96b3ee3e74828aceb4694b64f8571ba2210102c13aa1371ccbdd,
  0xd4bce472e9f101fc45d91c7bf2ae3afd1e6ab624290e473818b7991367ee3e83,
  0xbcd025634b2ee0689c7eb5947dfb35510633857df5e26473fb7d838410ff7aeb,
  0x8001e01e1f9f658c825a76e79312cfc281400015e77e8d2f4e88b795d8787801,
  0x0bac9b1267146082d524bceb51a8bc5a23779e1f95aca50bdfb904caf7649c66,
  0x8ee4e678e5cc1649e9585d391065444c7b7f267fb9a8db63a8415c6cea01d805,
  0xaff807573b47a5fadc2860030cd468b3dc2a7863938065ff9b4c009589b87730,
  0xb0e4cd427fa0a801713b376edc824e8fc3ddaba711714a2d3acd6cf5f04ccd3a,
  0xd955ff041528caeff94ef0a2fbc4ca60f5e5d4ae136a30160cf6683d17ac8f8d,
  0xe8ace1cefb782578a7288c6a6d7c95825d3f60206d5c3b7a62b7030c31a90a02,
  0xc4495c67c8b397386e30247b2f0dd57d54fbd866955840050b93165a3f20e680,
  0x0c4c7931203a388b4883209dd844bf671ff60e41739b225dd584e0755e61040b,
  0x466381270448f416ed95e36e9eab78c8ef2a3c488e84bb7c75c81688a487010a,
  0xfac52a9658589445b4454f0b85922a0bbca15b502a7db25bffb68f7934f0af5e,
  0xca463d4a94d0bd700566a162619f5adc420526bee768902ccc446b3a9d748b6d,
  0x4eed75ac3e0dd78016c22179e20cf890985fda0d159235c3ba159d7e7d614f08,
  0x220d42cb70d90fc3dd70a86bd73144d23ac84c42eccdb6365bd4ffb09b64be0b,
  0x0a93e6ea7c3563bcf4af104298869622c8752aaa690f10030157d7c932beb1a1,
  0xec8ce9116795d99396d19cb606111773085daf76c66d0d31d3936a09b5679301,
  0x5b1fe5cfd31c8e2737e676bb8adbf33c93f75f1b7cebe83aed7a8149e08f75f8,
  0x8cd799c7ec632f759c148edf9e3553afdda187bb86b6b1a68518f26ee3dc7f82,
  0x1a6d70640ecf80850f83790a01b88d3e353f817cbb1b2af8f188c743c45911b6,
  0x41e5abbf5ce2a2b7d01e0f4a191aa9a178c574831f3e3dc2d8ca18e8273fa967,
  0x5dbe44877df72e43bd66e6f5e55652118d39e781bca4c7ba657feb43d569fe6d,
  0x87b89d5b9455eb59f3171e6c80d892ffa5707db5d5aa6baf990bfa43ec2a101c,
  0x0075ccf40773897d145c260405f8040b95077689751fe2989db14a03cfebb546,
  0xffceb40a9b6c5eaba58128ba37f4d7308bd1e420c9959894448d5e0d4ae59631,
  0x6c1148e06ae2fa0d6e82b386b086ebf78eec322a9860d383875a67d667586f0e,
  0x274e9f5263784db9c0e1ffca7a42fd6876342530a846d74a54e8732388aad0f7,
  0x10c17f1af163fb054c61005b492ee5d5706fe298eccca4d56d9691ce7b2d106d,
  0x9327505ec4d790e9c129549a7d9b578e855a30dfa88b13f4aba3c3436a27846d,
  0x87a6797c7d0cc0f1ba1b49821e799548489d946c78c2b61a4a8a80a01bae0383,
  0x467054ec63c71122cbe8ee356fad2b7ca2808cdb339ac7f83ff59445aeab2362,
  0x3138d7d6b03286e47ba2c112cddbc45f002c33e91a50404ade7c95af28466a3a,
  0x9dfccc623948f751efc0660350d3dbe63b45bff05482c4931a31b663d19a5803,
  0x7dd9866f6d812e3e1dff75ee029712479cd03e8a761097a51bd0887c7d2d630d,
  0x10d3f42b96d408f6ae9879d6ca5b5680ade6cd3f2252a83835f4dfb6760d7285,
  0x7608198f16b92a4617a781f4d999576ed7068ef3204574ce08d25bc643ba92b6,
  0xfd29866b2548314f9704f1d2cb82a5553dfec2e928a360e4aa1f8f04fdfba62b,
  0x415d94b28b9ed9ac05d784603d24d5171899c27d2ade634a69cf4b5de4e1197d,
  0xa2286dd70c601fd8217bebd706f4f349013bf0c5ae5bc205775e56524e880db5,
  0xe639941a9e3d669fa2f38dc9af2d6e367832b85fd3796a9ad7d2ce30e76c78c3,
  0xa72a87186a69fd9c2ca2624633168fa6340237551e642646184dc2702f671b15,
  0x2fe1cec87ab96e5c5ce1bff90bfea883199a8f6af9fb2c3144e5dbcf0d2e6e31,
  0x358ea3dba42356a39a56072cabffbfc69a91def0de980d010b6891fdb4fb3342,
  0xdaeac125b56d2bfd0a33fbfb8240049c580af5ac678620629a131249ecb1de6d,
  0x9007a42dea2016e552d6ef9c545a61dc28196e2b0a58dc8ea17bccda272237a9,
  0x309e706530bbee4267e36b11f0daf383e7ac25a65288340c66731b25c73a9005,
  0x446bd0134cd1df8cfe8604b785fce9ce8fb44a2e9de28adeff468590f89f6228,
  0x9a9557a8a5dd3dcc450ea3441dfee4b28efd4bb117b712327a6508b62e688f8c,
  0x998a354ed840500315be44844b2d6a3d82ed35256adce1c4fe2833ace00083ad,
  0x9acb71d6de98d5ebafc6bb38427c01182cfa75b7c450881aedd054678426e02a,
  0x11acf4a2b3e2289393ce045e620e217993d248c1fee42c2bbf164b0aa781ccc0,
  0x126edbd80c37d687bb00544cba7c1d253a4b6fefa45c0d46cb9c54f31ede0c04,
  0x646b0b249d52782bbbc8cabf208cbce2b41a2871b5cdd7abe7ff8372be96654e,
  0xb39d074253e64d85fde4c2722400d272a288c2b127e18f896e826deaa0717af8,
  0xa17c92e4184fcb51ea7053309dd0c8ed5580c3ea568c242347a38153c800b4be,
  0x2e3897b8dc1e5f86bd4f92ef5f4a629d91a6cfdbe6377f7b4a3cd7e1ada2d2e7,
  0xb9636b340b3324ca5109058b71f6da21f0803b563112fff528d08ebcd1bb7e72,
  0x3afc7cb732d8f083eb42c7c1d59e8f80657bf4919e7f4233ef3e61b75e7c7f93,
  0x1a941f53b1b35d800feb7b6ff5d3b1aeb69dded2cefb6b9e69296f86fadc017d,
  0xe9fb8dcc3e73631e2a64a222a8dd62d8667b839cb2bf9340689e8a109803366c,
  0xb5801179812005be6ffa87f33567bf4873abf866aa7cc1932d4e984c3e98fc0f,
  0x3b0857625752a4bed77ca6865fb96fba2b0bf0c3e4b83371e34638d657460c04,
  0x1dbdbfc315968d915a15d381864593d8c6dc57cd0961e0ff01bf1660ed0bb94b,
  0x4c6ba3d1a750ff543cb70bd6ae65e9ab0a266de3e705c2e8086d770edd5a1581,
  0x6bb01cdec6e5a0278bd59373d4a91330fdee832b535e23d156d4817c0faad659,
  0x866adcf2e66140f00d7d0afb958101f42f30c3c2d79a936bab40956845aa7bc2,
  0x1fb9c39ffac53106471a9b260b5960064dcb338ebc028dee286ae8517757fe24,
  0x7a4aaa2e2831bdf5caa77e848250e1eb75a365aaeee7dfc975d675b0026c78ba,
  0xa6d10f647576a0bc8e191855d85e9c71131d3f0819110dac1a182c7e5590a2cf,
  0x7a6472b435853ab7a7d49793b10c6ca2b66dbc6c8e721ec5b968fd9b5e5a04e6,
  0x5e39c7d203dd9a8302fa113e3da0a3b3d87af871bc6d1e1a82d699db2bf20a7e,
  0x5aeac95de65bd98d49eb5194428a5a1a52c9827ea15f307205eaf026b67cd21c,
  0xdcbd72b07f7153f3588deec7b7fbaa3ac67c45c0e2d1d397cc53fb59e28d79c6,
  0x0d198153e1d54b8fd5372e90618a5fc98b0d093a0ad8be306bbf8941d7a7e268,
  0x27979d4eed9b0a28898bc1a04586f0dd90b697eccb53f4032937d927fea372a7,
  0x4179486ade570448d4d208f74217ba92667f0359bc03a31186fe60512e024324,
  0xb27f98b262718f39d1c75b7bdae84df783c6143f4ff9291c46fecc93c974a2ac,
  0x99947bf852fecc514311255582c918d72dd01f713820129ab6db3e611327a825,
  0xcd81af061e58be98ebd2128cb005062069a2a745c5ab1a7dbbf57dfb37206e0e,
  0x5e905890dad40d0f64e99ba5d5278aa7e9721ff9ccd8ca4e0f1c9f4714ef1793,
  0x91b0a5a1f51f03e8ec80a00f2844b3f9587d96381a19cd775e164a023e1aae05,
  0x13d823739b423aaa21299c2626e57b65b9a6773131f5fd5bf83a9a79d227904e,
  0x64c333979a95976bf94477e5b9993aba3c908bf890e99ba7d1c5df22277b799f,
  0xc7797bd197c3bc63d11f409ff57ec18b6f5fa3265894fdd080529d31cc1b00a2,
  0x839748f8527b78e24ad8db01202a6d19c1a4b279248c54c1e916980aaf900ac3,
  0xc4b79da6c325c44ab4c34b7abb7df48f5c72c4a170360dab43ef080f67230536,
  0xbfb39e358d3e3ec54832ee23237c8bdc278199a081bec0b446e2b600357f9c56,
  0xd345dc0027f54d06369d18ce839582037bcc4de938fcaa71371467abb7e945a5,
  0x97891548790cee35b306f71ad7c90e3ddc067dcf45e17124943f91d006de2063,
  0xf4ed645d32a5224da76f3d586cb17df797e6923813bdc84648adb4b92761703a,
  0x304f119f2dfa2851e4aafd8c0884862afb77222f376dd500cead56f2235826a3,
  0x61e193ae6f6600fa9799f7551ce789ae4ce483682ad375873d5b8d16d85db338,
  0x7791f09c4ca7d59f55835b3e1bb3e29eb94f6b2862eaae4bacbe859e323172ef,
  0xeea8066d4256a0c85096aeb64406c494716fc7c7aa96e5271c6adb662e4c3fd2,
  0xe292287aa4833432d0a2fad26673b11e533ffa03752365155d2366f29d3790b3,
  0xb6293eff4bc30337c211b6094bde104dc078e4a1eb985d7de25bcfca6cd7d8bf,
  0xb860663c21d8516b796d39b39dc70af4fe949afd48ef38131c0a457be1626413,
  0x4d8855a62bacbaa67ebc25e3a67072d2bf614624cf25ffa22b4ac6d64f74e9fc,
  0xa0f89fb0ff469b5955a693873fb7c711115b4b03e0dc8fe05a554d5b800b224a,
  0xe521ba4be887fdbaf978a64c4fb85b1b9f834ea70a4eb82ee6325bd6f9e35e90,
  0x5d0b6c60d166f26f9d97615d55f3217e378685c07f64210e65e837c0bdbaaa3e,
  0x72aa4a50414a5faa7e26958fb9216b1196ff04240ceb680f0a20442907ca9c1b,
  0x025b66a5cfc1d486085906fd071331fd48b97e2fb67cc0eb6d1c8356dc7584c2,
  0x63dc7780565c42803af4c49a84005620b7fc31057e4488f383bd6499bd3bfadf,
  0x00bdb3db47b5b6aebe007b80b34c80da42388f63b238e4e856333a2856b37468,
  0x4579755d10f7c55690461db968ebdd90e4b6b609e8767bb51f2dedbae1a5ebc4,
  0x0527d0bc856eb799ecb55cde566e11024b5693578b23d522a72a2e0dff8a6413,
  0x82632a594fc20bc2a237a43c79364b57a7456d96670c2a6372998eba8087ddea,
  0xf58a91de2a58da72e196609d187214ccd27b931c4a4259933070bb0c1efefa85,
  0x77ad071973e16d6d513d8a6bdafa572a5fe0727908e482617f0030e91b6db4ad,
  0x0cd679d9f3fc4af91e4ef8380d279c6d5ce187ae61c83c89cb9045fb3ba40784,
  0xcdba2ac85a879bf8eb9e45bb6a6162e3a7b3731124992be4b10b0d3724b8bbf3,
  0xffd35018fc012692274d306206fb3122476cf0e64954241a50dda631d889ce8d,
  0x78f09b7aed430a3b8cdac62383e39d394d09d19fa4744e663059edd77aae4040,
  0x2b8f93143e35456eee7b0a93f51b524fee4db5e302ba4e42a1a7b3901cc37fe0,
  0x2deada5c1e74464cab8082bf29c634d8e9b368289a961c2ef2f6839fb2d31e0a,
  0xfae393db740dcc42aa75f021d15f27b4323944dbb17d44823c00c75c2267f83b,
  0x3ef74d19b10176d0018f08127c24525916d5e41112cec288f754820ba02ab88d,
  0x1244ac860386b812256c6236536c6a290341e60a48a34009b187ad25c4f1c322,
  0xcb6c84b3c9acf542a6629a4e82233bb76adef84fd80bcc647fef73a655ecb4bd,
  0x2e74a3ce2cc110e88e22641c7d3346d61bc06b2cb4519a4e58d8350c7b5bb3dc,
  0xe887272be342fccaa17e9a84d2e09702790a137e14bfa851676b4420cbbeb8ef,
  0xb863d110a420704c9a793d8f825c7448b73552d91df5efdca84edf5b50ae7a44,
  0xa7091d425ce1bcaa454ff89b23f1eb59fd4ac6dcf2ddf57e78633e02ccf707ef,
  0xb1c20a6de271a7366ee6d737454bf1735d420cc02844749e1fa3a4000af50e18,
  0x6b948575850c1b22c5471e4f90ae68a9439219e63b2c7f5b372f6dc7852f1e0a,
  0xb5a44079be7938669b7b38245cbb219f6f968469710dbcaecd29106474ead633,
  0x3ee376558296e48ee56fe4a198ebe841101fed23daf7e98b5a64e20f0c6159c2,
  0x62b9d7ccf126f5d0501b99b9d014603b046a47d6e86ddb65484bf5d3c0f8bf9e
]

private def evalBinvGo : Nat → List Nat → Nat → Nat
  | _, [], acc => acc
  | v, b :: bs, acc =>
    let acc1 := if v &&& 1 == 1 then acc ^^^ b else acc
    evalBinvGo (v >>> 1) bs acc1

def evalBinv (v : Nat) : Nat := evalBinvGo v invBasisList 0

private def checkInvBasisB : Nat → List Nat → Bool
  | _, [] => true
  | idx, b :: bs => (evalPoly b == 1 <<< idx) && checkInvBasisB (idx + 1) bs

private def checkInvBasisLeftAt : Nat → Nat → Nat → Bool
  | _, 0, _ => true
  | k, n + 1, cur =>
    (evalBinv cur == 1 <<< k) && checkInvBasisLeftAt (k + 1) n (stepNat cur)

private def primeFactors256 : List Nat := [
  3, 5, 17, 257, 641, 65537, 274177, 6700417,
  67280421310721, 59649589127497217, 5704689200685129054721
]

private def checkTree (g : Nat) : Nat → List Nat → Bool
  | 0, _ => false
  | _, [] => true
  | _, [_] => g != 1
  | fuel + 1, ps =>
    let half := ps.length / 2
    let left := ps.take half
    let right := ps.drop half
    checkTree (polyPow g (List.prod right)) fuel left &&
      checkTree (polyPow g (List.prod left)) fuel right

set_option maxRecDepth 8192 in
private theorem spread16_basis_all :
    (List.range 256).all (fun i => spread16 (1 <<< i) == 1 <<< (16 * i)) = true := by
  decide

set_option maxRecDepth 8192 in
private theorem compress16_basis_all :
    (List.range 512).all (fun k => compress16 (1 <<< (16 * k)) == 1 <<< k) = true := by
  decide

private theorem barrett_rem_bound :
    ((clMul barrettQ0 pLow ^^^ (barrettQ0 <<< 256)) ^^^ (1 <<< 511)) < 2 ^ 256 := by
  decide

set_option maxRecDepth 8192 in
private theorem charpoly_check : evalPoly pLow = iterStep 256 1 := by decide

set_option maxRecDepth 8192 in
private theorem b_invbasis_check : checkInvBasisB 0 invBasisList = true := by decide

set_option maxRecDepth 8192 in
private theorem b_invbasis_left_check : checkInvBasisLeftAt 0 256 1 = true := by decide

set_option maxRecDepth 8192 in
private theorem pow_period_one : polyPow 2 (2 ^ 256 - 1) = 1 := by decide

set_option maxRecDepth 8192 in
private theorem tree_check : checkTree 2 6 primeFactors256 = true := by decide

private theorem primeFactors256_prod : primeFactors256.prod = 2 ^ 256 - 1 := by decide

private theorem pLow_lt : pLow < 2 ^ 256 := by decide
private theorem barrettQ0_lt : barrettQ0 < 2 ^ 256 := by decide
set_option maxRecDepth 8192 in
private theorem invBasisList_len : invBasisList.length = 256 := by decide

set_option maxRecDepth 32768 in
private theorem invBasisList_shift_lt :
    invBasisList.all (fun b => b >>> 256 == 0) = true := by
  decide

private theorem invBasisList_lt :
    invBasisList.all (fun b => decide (b < 2 ^ 256)) = true := by
  rw [List.all_eq_true]
  intro b hb
  have hS := eq_of_beq ((List.all_eq_true.mp invBasisList_shift_lt) b hb)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hS
  rcases hS with h0 | hLt
  · exact absurd h0 (by decide)
  · exact decide_eq_true hLt

private theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide) h

private theorem pow255_pos : 0 < 2 ^ 255 := Nat.two_pow_pos 255
private theorem pow256_pos : 0 < 2 ^ 256 := Nat.two_pow_pos 256
private theorem one_lt_pow256 : 1 < 2 ^ 256 := Nat.one_lt_two_pow (by decide)
private theorem two_lt_pow256 : 2 < 2 ^ 256 := two_pow_lt_two_pow (by decide : 1 < 256)
private theorem pow256_sub_one_pos : 0 < 2 ^ 256 - 1 := Nat.sub_pos_of_lt one_lt_pow256
private theorem pow256_sub_one_lt : 2 ^ 256 - 1 < 2 ^ 256 := Nat.sub_lt pow256_pos (by decide)
private theorem pow256_lt_pow257 : 2 ^ 256 < 2 ^ 257 := two_pow_lt_two_pow (by decide : 256 < 257)

private theorem mask255_def : mask255 = (1 <<< 255) - 1 := rfl
private theorem mask256_def : mask256 = (1 <<< 256) - 1 := rfl

private theorem mask255_eq : mask255 = 2 ^ 255 - 1 := by
  simp only [mask255, Nat.shiftLeft_eq, Nat.one_mul]

private theorem mask256_eq : mask256 = 2 ^ 256 - 1 := by
  simp only [mask256, Nat.shiftLeft_eq, Nat.one_mul]

private theorem and_mask255_lt (x : Nat) : x &&& mask255 < 2 ^ 255 := by
  rw [mask255_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ pow255_pos

private theorem and_mask256_lt (x : Nat) : x &&& mask256 < 2 ^ 256 := by
  rw [mask256_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ pow256_pos

private theorem and_mask256_testBit (x k : Nat) :
    (x &&& mask256).testBit k = (decide (k < 256) && x.testBit k) := by
  rw [mask256_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Bool.and_comm]

private theorem lor_and (a b m : Nat) : (a ||| b) &&& m = (a &&& m) ||| (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit k <;> cases b.testBit k <;> cases m.testBit k <;> rfl

private theorem lor_shiftLeft (a b s : Nat) : (a ||| b) <<< s = (a <<< s) ||| (b <<< s) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : s ≤ k <;> simp [h]

private theorem lor_shiftRight (a b s : Nat) : (a ||| b) >>> s = (a >>> s) ||| (b >>> s) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [Nat.testBit_or, Nat.testBit_shiftRight]

private theorem or_distrib_stepL (a b mLo mHi s : Nat) :
    ((a ||| b) &&& mLo) ||| (((a ||| b) &&& mHi) <<< s) =
      ((a &&& mLo) ||| ((a &&& mHi) <<< s)) ||| ((b &&& mLo) ||| ((b &&& mHi) <<< s)) := by
  rw [lor_and, lor_and, lor_shiftLeft]
  ac_rfl

private theorem or_distrib_stepR (a b mLo mHi s : Nat) :
    ((a ||| b) &&& mLo) ||| (((a ||| b) &&& mHi) >>> s) =
      ((a &&& mLo) ||| ((a &&& mHi) >>> s)) ||| ((b &&& mLo) ||| ((b &&& mHi) >>> s)) := by
  rw [lor_and, lor_and, lor_shiftRight]
  ac_rfl

private theorem sStep_lor (mLo mHi s a b : Nat) :
    sStep mLo mHi s (a ||| b) = sStep mLo mHi s a ||| sStep mLo mHi s b :=
  or_distrib_stepL a b mLo mHi s

private theorem cStep_lor (mLo mHi s a b : Nat) :
    cStep mLo mHi s (a ||| b) = cStep mLo mHi s a ||| cStep mLo mHi s b :=
  or_distrib_stepR a b mLo mHi s

private theorem spread16_zero : spread16 0 = 0 := by decide

private theorem spread16_lor (a b : Nat) : spread16 (a ||| b) = spread16 a ||| spread16 b := by
  unfold spread16
  simp only [sStep_lor]

private theorem compress16_zero : compress16 0 = 0 := by decide

private theorem compress16_lor (a b : Nat) :
    compress16 (a ||| b) = compress16 a ||| compress16 b := by
  unfold compress16
  rw [lor_and]
  simp only [cStep_lor]

private theorem compress16_mask (y : Nat) : compress16 (y &&& lane0Mask) = compress16 y := by
  unfold compress16
  have hIdem : (y &&& lane0Mask) &&& lane0Mask = y &&& lane0Mask := by
    apply Nat.eq_of_testBit_eq
    intro k
    simp [Nat.testBit_and]
  rw [hIdem]

private theorem add_eq_lor_of_disjoint_aux :
    ∀ n a b : Nat,
      a + b ≤ n → (∀ k, (a.testBit k && b.testBit k) = false) → a + b = a ||| b
  | 0, a, b, hle, _ => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; rfl
  | n + 1, a, b, hle, hDisj => by
    by_cases hab : a = 0 ∧ b = 0
    · rcases hab with ⟨rfl, rfl⟩; rfl
    · have h0 := hDisj 0
      simp only [Nat.testBit_zero] at h0
      have hBoth : ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
        intro ⟨ha, hb⟩; simp [ha, hb] at h0
      have hRec := add_eq_lor_of_disjoint_aux n (a / 2) (b / 2) (by omega) (fun k => by
        simpa [Nat.testBit_succ] using hDisj (k + 1))
      have hOrDiv : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro k
        rw [← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_or, Nat.testBit_succ,
          Nat.testBit_succ]
      have hOrMod : (a ||| b) % 2 = a % 2 + b % 2 := by
        have hbt : (a ||| b).testBit 0 = (a.testBit 0 || b.testBit 0) := Nat.testBit_or a b 0
        simp only [Nat.testBit_zero] at hbt
        have ha2 := Nat.mod_two_eq_zero_or_one a
        have hb2 := Nat.mod_two_eq_zero_or_one b
        have ho2 := Nat.mod_two_eq_zero_or_one (a ||| b)
        rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;>
          rcases ho2 with ho | ho <;> simp_all
      omega

private theorem add_eq_lor_of_disjoint {a b : Nat}
    (hDisj : ∀ k, (a.testBit k && b.testBit k) = false) : a + b = a ||| b :=
  add_eq_lor_of_disjoint_aux (a + b) a b (le_refl _) hDisj

private theorem testBit_two_pow_mul (a s k : Nat) :
    (a * 2 ^ s).testBit k = if k < s then false else a.testBit (k - s) := by
  rw [← Nat.shiftLeft_eq]
  simp only [Nat.testBit_shiftLeft]
  by_cases h : k < s
  · simp [show ¬ s ≤ k by omega]
  · simp [show s ≤ k by omega]

private theorem testBit_sum_pow_mul (m : Nat) (hm : 0 < m) (P : Nat → Bool) :
    ∀ (S : Finset Nat) (k : Nat),
      (∑ i ∈ S, if P i then 2 ^ (m * i) else 0).testBit k =
        decide (∃ i ∈ S, k = m * i ∧ P i = true) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro k; simp
  | @insert a U ha ih =>
    intro k
    have hDisj : ∀ t, ((if P a then 2 ^ (m * a) else 0).testBit t &&
        (∑ i ∈ U, if P i then 2 ^ (m * i) else 0).testBit t) = false := by
      intro t
      by_cases ht : t = m * a
      · subst ht
        have hF : (∑ i ∈ U, if P i then 2 ^ (m * i) else 0).testBit (m * a) = false := by
          rw [ih]
          exact decide_eq_false (fun ⟨i, hi, heq, _⟩ =>
            ha ((Nat.eq_of_mul_eq_mul_left hm heq) ▸ hi))
        rw [hF, Bool.and_false]
      · have hF : (if P a then 2 ^ (m * a) else 0).testBit t = false := by
          split <;> simp [show m * a ≠ t by omega]
        rw [hF, Bool.false_and]
    rw [Finset.sum_insert ha, add_eq_lor_of_disjoint hDisj, Nat.testBit_or, ih]
    by_cases hk : k = m * a
    · subst hk
      by_cases hpa : P a = true
      · simp [hpa]
      · simp [Bool.eq_false_iff.mpr hpa]
    · have hF : (if P a then 2 ^ (m * a) else 0).testBit k = false := by
        split <;> simp [show m * a ≠ k by omega]
      simp [hF, hk]

private def foldOr : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, g => g n ||| foldOr n g

private theorem foldOr_congr :
    ∀ {n : Nat} {g1 g2 : Nat → Nat}, (∀ i < n, g1 i = g2 i) → foldOr n g1 = foldOr n g2
  | 0, _, _, _ => rfl
  | n + 1, g1, g2, h => by
    simp only [foldOr, h n (Nat.lt_succ_self n),
      foldOr_congr fun i hi => h i (Nat.lt_succ_of_lt hi)]

private theorem range_fold_lor_pow (f : Nat → Nat) (hf0 : f 0 = 0)
    (hfLor : ∀ x y, f (x ||| y) = f x ||| f y) (m mult N : Nat) (hm : 0 < m)
    (P : Nat → Bool) (hfBasis : ∀ i < N, f (1 <<< (mult * i)) = 2 ^ (m * i)) :
    ∀ M ≤ N,
      f (foldOr M (fun i => if P i then 1 <<< (mult * i) else 0)) =
        ∑ i ∈ Finset.range M, if P i then 2 ^ (m * i) else 0 := by
  intro M hMN
  induction M with
  | zero => simp [foldOr, hf0]
  | succ k ih =>
    simp only [foldOr]
    rw [hfLor, Finset.sum_range_succ, ih (by omega)]
    have hkLt : k < N := by omega
    have hT : f (if P k then 1 <<< (mult * k) else 0) = if P k then 2 ^ (m * k) else 0 := by
      split
      · exact hfBasis k hkLt
      · exact hf0
    rw [hT, Nat.add_comm]
    symm
    apply add_eq_lor_of_disjoint
    intro t
    rw [testBit_sum_pow_mul m hm P (Finset.range k) t]
    by_cases ht : t = m * k
    · subst ht
      have hF : decide (∃ i ∈ Finset.range k, m * k = m * i ∧ P i = true) = false :=
        decide_eq_false (fun ⟨i, hi, heq, _⟩ => by
          have := Finset.mem_range.mp hi
          have := Nat.eq_of_mul_eq_mul_left hm heq
          omega)
      rw [hF, Bool.and_false]
    · have hF : (if P k then 2 ^ (m * k) else 0).testBit t = false := by
        split <;> simp [show m * k ≠ t by omega]
      rw [hF, Bool.false_and]

private theorem nat_decomp_lor (n : Nat) :
    ∀ x, x < 2 ^ n →
      x = foldOr n (fun i => if x.testBit i then 1 <<< i else 0) := by
  induction n with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    rfl
  | succ m ih =>
    intro x hx
    let lo := x &&& ((1 <<< m) - 1)
    have hLoLt : lo < 2 ^ m := by
      simp only [lo, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos m)
    have hLoBit : ∀ i < m, lo.testBit i = x.testBit i := by
      intro i hi
      simp only [lo, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
        Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
    have hLoEq :
        foldOr m (fun i => if x.testBit i then 1 <<< i else 0) =
        foldOr m (fun i => if lo.testBit i then 1 <<< i else 0) :=
      foldOr_congr fun i hi => by rw [hLoBit i hi]
    rw [foldOr, hLoEq, ← ih lo hLoLt]
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_or, lo, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
    by_cases hm : k = m
    · subst hm
      simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.or_false]
      split_ifs with hbit <;> simp [hbit]
    · by_cases hkm : k < m
      · have hB : (if x.testBit m = true then 2 ^ m else 0).testBit k = false := by
          split <;> simp [show m ≠ k by omega]
        simp [hkm, hB]
      · have hGe : m + 1 ≤ k := by omega
        have hXFalse : x.testBit k = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hGe))
        have hB : (if x.testBit m = true then 2 ^ m else 0).testBit k = false := by
          split <;> simp [show m ≠ k by omega]
        simp [hkm, hXFalse, hB]

private theorem lt_two_pow_of_testBit_eq_false {x K : Nat}
    (h : ∀ k, K ≤ k → x.testBit k = false) : x < 2 ^ K := by
  by_contra hGe
  have hPos : x ≠ 0 := by
    intro hz; subst hz; exact hGe (Nat.two_pow_pos K)
  have hLog : K ≤ Nat.log2 x := (Nat.le_log2 hPos).mpr (by omega)
  have hTrue := Nat.testBit_log2 hPos
  rw [h (Nat.log2 x) hLog] at hTrue
  contradiction

private theorem spread16_spec (x : Nat) (hx : x < 2 ^ 256) :
    spread16 x = ∑ i ∈ Finset.range 256, if x.testBit i then 2 ^ (16 * i) else 0 := by
  have hB : ∀ i < 256, spread16 (1 <<< (1 * i)) = 2 ^ (16 * i) := fun i hi => by
    have hAll := eq_of_beq ((List.all_eq_true.mp spread16_basis_all) i (List.mem_range.mpr hi))
    simpa [Nat.shiftLeft_eq, Nat.one_mul] using hAll
  calc spread16 x
      = spread16 (foldOr 256
          (fun i => if x.testBit i then 1 <<< (1 * i) else 0)) := by
            simp only [Nat.one_mul]; rw [← nat_decomp_lor 256 x hx]
    _ = _ := range_fold_lor_pow spread16 spread16_zero spread16_lor 16 1 256 (by decide) _ hB
          256 (le_refl 256)

private def polyCoeffSum (a b k : Nat) : Nat :=
  ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
    if i + j = k ∧ a.testBit i ∧ b.testBit j then 1 else 0

private theorem polyCoeffSum_le (a b k : Nat) : polyCoeffSum a b k ≤ 256 := by
  unfold polyCoeffSum
  calc ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
        (if i + j = k ∧ a.testBit i ∧ b.testBit j then 1 else 0)
      ≤ ∑ i ∈ Finset.range 256, 1 := by
        apply Finset.sum_le_sum; intro i _
        by_cases hi : k - i < 256 ∧ i ≤ k
        · rw [Finset.sum_eq_single (k - i)]
          · split_ifs <;> omega
          · intro j _ hne; split_ifs with h <;> first | rfl | omega
          · intro habs; exfalso; exact habs (Finset.mem_range.mpr hi.1)
        · exact Nat.le_trans (Nat.le_of_eq (Finset.sum_eq_zero fun j hj => by
            split_ifs with h <;> first | rfl | (exfalso; have := Finset.mem_range.mp hj; omega)))
            (Nat.zero_le 1)
    _ = 256 := by simp

private theorem testBit_chunked_sum (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 16) :
    ∀ (N t : Nat),
      (∑ k ∈ Finset.range N, f k * 2 ^ (16 * k)).testBit t =
        if t / 16 < N then (f (t / 16)).testBit (t % 16) else false := by
  intro N
  induction N with
  | zero => intro t; simp
  | succ m ih =>
    intro t
    have hDisj : ∀ k, ((∑ x ∈ Finset.range m, f x * 2 ^ (16 * x)).testBit k &&
        (f m * 2 ^ (16 * m)).testBit k) = false := by
      intro k
      rw [ih k, testBit_two_pow_mul]
      by_cases hk : k < 16 * m
      · simp [hk]
      · simp [show ¬ k / 16 < m by omega]
    rw [Finset.sum_range_succ, add_eq_lor_of_disjoint hDisj, Nat.testBit_or, ih t,
      testBit_two_pow_mul]
    by_cases htm : t / 16 < m
    · have hF : (if t < 16 * m then false else (f m).testBit (t - 16 * m)) = false := by
        split_ifs with hlt
        · rfl
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf m)
            (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [htm, ↓reduceIte, Nat.lt_succ_of_lt htm, hF, Bool.or_false]
    · by_cases heq : t / 16 = m
      · have hmod : t - 16 * m = t % 16 := by omega
        have hNotLt : ¬ t < 16 * m := by omega
        have hLt1 : m < m + 1 := Nat.lt_succ_self m
        simp [heq, hNotLt, hmod, hLt1]
      · have hNotLt2 : ¬ t / 16 < m + 1 := by omega
        simp only [htm, ↓reduceIte, hNotLt2, Bool.false_or]
        split_ifs with hlt
        · rfl
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf m)
            (Nat.pow_le_pow_right (by decide) (by omega)))

private theorem repMask_testBit :
    ∀ (k acc s W u : Nat), 0 < s → 0 < W →
      (∀ t, acc.testBit t = decide (t % s = 0 ∧ t / s < W)) →
      (repMask acc (s * W) k).testBit u = decide (u % s = 0 ∧ u / s < 2 ^ k * W)
  | 0, acc, s, W, u, _, _, hAcc => by simpa [repMask] using hAcc u
  | k + 1, acc, s, W, u, hs, hW, hAcc => by
    unfold repMask
    rw [show 2 * (s * W) = s * (2 * W) by ring]
    have hNext : ∀ t, (acc ||| (acc <<< (s * W))).testBit t =
        decide (t % s = 0 ∧ t / s < 2 * W) := by
      intro t
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hAcc t]
      by_cases hlt : t < s * W
      · have hNotLe : ¬ s * W ≤ t := by omega
        have hDivLt : t / s < W :=
          (Nat.div_lt_iff_lt_mul hs).mpr (by rw [Nat.mul_comm]; exact hlt)
        have hDiv2 : t / s < 2 * W := by omega
        simp [hNotLe, hDivLt, hDiv2]
      · have hLe : s * W ≤ t := by omega
        have hNotDiv : ¬ t / s < W := by
          intro hLt; have hM := (Nat.div_lt_iff_lt_mul hs).mp hLt; rw [Nat.mul_comm] at hM; omega
        rw [hAcc (t - s * W)]
        have hSub : (t - s * W) % s = t % s := by
          have hEq : t = (t - s * W) + s * W := (Nat.sub_add_cancel hLe).symm
          conv_rhs => rw [hEq]
          rw [Nat.add_mul_mod_self_left]
        have hDivSub : (t - s * W) / s < W ↔ t / s < 2 * W := by
          rw [Nat.div_lt_iff_lt_mul hs, Nat.div_lt_iff_lt_mul hs]
          have hMul : 2 * W * s = 2 * (s * W) := by ring
          rw [hMul, Nat.mul_comm W s]
          omega
        simp [hLe, hNotDiv, hSub, hDivSub]
    have hRec := repMask_testBit k (acc ||| (acc <<< (s * W))) s (2 * W) u hs (by omega) hNext
    rw [hRec, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 W, ← Nat.mul_assoc (2 ^ k)]

private theorem lane0Mask_testBit (u : Nat) :
    lane0Mask.testBit u = decide (u % 16 = 0 ∧ u / 16 < 512) := by
  have hOne : ∀ t, (1 : Nat).testBit t = decide (t % 16 = 0 ∧ t / 16 < 1) := by
    intro t
    by_cases ht : t = 0
    · subst ht; decide
    · have hBit : (1 : Nat).testBit t = false :=
        Bool.eq_false_iff.mpr fun h => ht (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
      rw [hBit]
      symm
      exact decide_eq_false fun ⟨hM, hD⟩ => ht (by omega)
  have hRes := repMask_testBit 9 1 16 1 u (by decide) (by decide) hOne
  simpa [lane0Mask] using hRes

private theorem clMul_testBit (a b k : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (clMul a b).testBit k = decide (k < 512 ∧ polyCoeffSum a b k % 2 = 1) := by
  let S : Nat := ∑ j ∈ Finset.range 512, polyCoeffSum a b j * 2 ^ (16 * j)
  have hProd : spread16 a * spread16 b = S := by
    rw [spread16_spec a ha, spread16_spec b hb, Finset.sum_mul]
    simp only [Finset.mul_sum]
    calc ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
          (if a.testBit i then 2 ^ (16 * i) else 0) *
            (if b.testBit j then 2 ^ (16 * j) else 0)
        = ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
            (if a.testBit i ∧ b.testBit j then 1 else 0) * 2 ^ (16 * (i + j)) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          by_cases h1 : a.testBit i <;> by_cases h2 : b.testBit j <;>
            simp [h1, h2, Nat.pow_add, Nat.mul_add]
      _ = ∑ u ∈ Finset.range 512, polyCoeffSum a b u * 2 ^ (16 * u) := by
          simp only [polyCoeffSum, Finset.sum_mul]
          have hSwap :
              ∑ i ∈ Finset.range 256, ∑ u ∈ Finset.range 512, ∑ j ∈ Finset.range 256,
                (if i + j = u ∧ a.testBit i ∧ b.testBit j then 1 else 0) * 2 ^ (16 * u) =
              ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
                (if a.testBit i ∧ b.testBit j then 1 else 0) * 2 ^ (16 * (i + j)) := by
            apply Finset.sum_congr rfl; intro i hi
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j hj
            have hiLt := Finset.mem_range.mp hi
            have hjLt := Finset.mem_range.mp hj
            rw [Finset.sum_eq_single (i + j)]
            · simp
            · intro u _ hne; simp [Ne.symm hne]
            · intro habs; exfalso; exact habs (Finset.mem_range.mpr (by omega))
          rw [← hSwap, Finset.sum_comm]
  have hBound : ∀ j, polyCoeffSum a b j < 2 ^ 16 := fun j =>
    lt_of_le_of_lt (polyCoeffSum_le a b j) (by decide)
  have hFoldBit : ∀ (M : Nat) (t : Nat),
      (foldOr M
        (fun j => if polyCoeffSum a b j % 2 == 1 then 1 <<< (16 * j) else 0)).testBit t =
        decide (t / 16 < M ∧ t % 16 = 0 ∧ polyCoeffSum a b (t / 16) % 2 = 1) := by
    intro M t
    induction M with
    | zero => simp [foldOr]
    | succ r ih =>
      rw [foldOr, Nat.testBit_or, ih]
      by_cases hm : t = 16 * r
      · subst hm
        by_cases hp : polyCoeffSum a b r % 2 = 1 <;>
          simp [hp, Nat.shiftLeft_eq,
            show (16 * r) / 16 = r by omega, show (16 * r) % 16 = 0 by omega]
      · have hB : (if polyCoeffSum a b r % 2 == 1 then 1 <<< (16 * r) else 0).testBit t =
            false := by
          split_ifs <;> simp [Nat.shiftLeft_eq, show 16 * r ≠ t by omega]
        rw [hB, Bool.false_or]
        by_cases h0 : t % 16 = 0
        · have hNe : t / 16 ≠ r := by omega
          simp [h0, show t / 16 < r + 1 ↔ t / 16 < r by omega]
        · simp [h0]
  have hLane0 : S &&& lane0Mask =
      foldOr 512
        (fun j => if polyCoeffSum a b j % 2 == 1 then 1 <<< (16 * j) else 0) := by
    apply Nat.eq_of_testBit_eq; intro t
    rw [Nat.testBit_and, testBit_chunked_sum _ hBound, lane0Mask_testBit, hFoldBit]
    by_cases hLt : t / 16 < 512 <;> by_cases hM : t % 16 = 0
    · simp only [hLt, hM, ↓reduceIte]
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one (polyCoeffSum a b (t / 16)) with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp [hLt, hM]
    · simp [hLt, hM]
    · simp [hLt, hM]
  have hBComp : ∀ j < 512, compress16 (1 <<< (16 * j)) = 2 ^ (1 * j) := fun j hj => by
    have hAll := eq_of_beq ((List.all_eq_true.mp compress16_basis_all) j (List.mem_range.mpr hj))
    simpa [Nat.shiftLeft_eq, Nat.one_mul] using hAll
  have hComp : clMul a b =
      ∑ j ∈ Finset.range 512, if polyCoeffSum a b j % 2 == 1 then 2 ^ (1 * j) else 0 := by
    unfold clMul
    rw [hProd, ← compress16_mask, hLane0]
    exact range_fold_lor_pow compress16 compress16_zero compress16_lor 1 16 512 (by decide) _
      hBComp 512 (le_refl 512)
  rw [hComp]
  have hTB := testBit_sum_pow_mul 1 (by decide) (fun j => polyCoeffSum a b j % 2 == 1)
    (Finset.range 512) k
  simpa using hTB

private theorem clMul_lt_pow {a b M N K : Nat} (_hM0 : 0 < M) (_hN0 : 0 < N)
    (hM : M ≤ 256) (hN : N ≤ 256) (hK : M + N - 1 = K) (ha : a < 2 ^ M) (hb : b < 2 ^ N) :
    clMul a b < 2 ^ K := by
  subst hK
  apply lt_two_pow_of_testBit_eq_false
  intro k hk
  have ha256 : a < 2 ^ 256 := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hM)
  have hb256 : b < 2 ^ 256 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hN)
  rw [clMul_testBit a b k ha256 hb256]
  have hSum0 : polyCoeffSum a b k = 0 := by
    unfold polyCoeffSum
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with h
    · exfalso
      rcases h with ⟨hij, hai, hbj⟩
      have hiLt : i < M := by
        by_contra hGe
        have hF := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega : M ≤ i)))
        rw [hF] at hai
        contradiction
      have hjLt : j < N := by
        by_contra hGe
        have hF := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega : N ≤ j)))
        rw [hF] at hbj
        contradiction
      omega
    · rfl
  simp [hSum0]

private noncomputable def natToPoly : Nat → Polynomial (ZMod 2)
  | 0 => 0
  | n + 1 =>
    Polynomial.C (((n + 1) % 2 : Nat) : ZMod 2) + Polynomial.X * natToPoly ((n + 1) / 2)
  termination_by n => n

private theorem natToPoly_coeff (n k : Nat) :
    (natToPoly n).coeff k = if n.testBit k then 1 else 0 := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [natToPoly]
    | succ m =>
      rw [natToPoly]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
        add_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one (m + 1) with h0 | h1
      · simp [h0]
      · simp [h1]
  | succ r ih =>
    cases n with
    | zero => simp [natToPoly]
    | succ m =>
      rw [natToPoly]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add, Polynomial.coeff_X_mul,
        ih ((m + 1) / 2), Nat.testBit_succ]

private theorem natToPoly_inj {a b : Nat} (h : natToPoly a = natToPoly b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := congrArg (fun p : Polynomial (ZMod 2) => p.coeff k) h
  rw [natToPoly_coeff, natToPoly_coeff] at hk
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all

private theorem natToPoly_zero : natToPoly 0 = 0 := by simp [natToPoly]

private theorem natToPoly_one : natToPoly 1 = 1 := by
  ext k
  rw [natToPoly_coeff, Polynomial.coeff_one]
  cases k with
  | zero => simp
  | succ r => simp [Nat.testBit_one_eq_true_iff_self_eq_zero]

private theorem natToPoly_two : natToPoly 2 = Polynomial.X := by
  ext k
  rw [natToPoly_coeff, Polynomial.coeff_X]
  rcases k with _ | _ | r
  · simp [show Nat.testBit 2 0 = false by decide]
  · simp [show Nat.testBit 2 1 = true by decide]
  · have hF : Nat.testBit 2 (r + 2) = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hF]

private theorem natToPoly_xor (a b : Nat) :
    natToPoly (a ^^^ b) = natToPoly a + natToPoly b := by
  ext k
  simp only [Polynomial.coeff_add, natToPoly_coeff, Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> decide

private theorem poly_add_self_zmod2 (p : Polynomial (ZMod 2)) : p + p = 0 := by
  ext k
  simp only [Polynomial.coeff_add, Polynomial.coeff_zero]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, h2, zero_mul]

private theorem natToPoly_shiftLeft (n s : Nat) :
    natToPoly (n <<< s) = natToPoly n * Polynomial.X ^ s := by
  ext k
  rw [natToPoly_coeff, Nat.testBit_shiftLeft, Polynomial.coeff_mul_X_pow']
  by_cases h : s ≤ k
  · simp [h, natToPoly_coeff]
  · simp [h]

private theorem natToPoly_shiftRight_add (n s : Nat) :
    natToPoly n = natToPoly (n >>> s) * Polynomial.X ^ s + natToPoly (n &&& ((1 <<< s) - 1)) := by
  ext k
  simp only [Polynomial.coeff_add, natToPoly_coeff, Polynomial.coeff_mul_X_pow',
    Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : s ≤ k
  · have hk : ¬ k < s := by omega
    simp [h, hk, Nat.add_sub_cancel' h]
  · have hk : k < s := by omega
    simp [h, hk, Nat.testBit_mod_two_pow]

private theorem poly_finset_sum_coeff {ι : Type} (s : Finset ι)
    (f : ι → Polynomial (ZMod 2)) (k : Nat) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a U ha _ => simp [Finset.sum_insert ha]

private theorem natToPoly_degree_lt (n N : Nat) (hn : n < 2 ^ N) :
    (natToPoly n).degree < (N : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [natToPoly_coeff]
  have hF : n.testBit m = false := Nat.testBit_lt_two_pow
    (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hm))
  simp [hF]

private theorem natToPoly_eq_sum (x N : Nat) (hx : x < 2 ^ N) :
    natToPoly x = ∑ i ∈ Finset.range N, if x.testBit i then Polynomial.X ^ i else 0 := by
  ext k
  rw [natToPoly_coeff, poly_finset_sum_coeff]
  by_cases hk : k < N
  · rw [Finset.sum_eq_single k]
    · split <;> simp
    · intro b _ hne
      split <;> simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro habs; exfalso; exact habs (Finset.mem_range.mpr hk)
  · have hF : x.testBit k = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hbLt := Finset.mem_range.mp hb
    split
    · simp [Polynomial.coeff_X_pow, show k ≠ b by omega]
    · simp

private theorem natCast_zmod2 (m : Nat) :
    ((m : Nat) : ZMod 2) = if m % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    subst hk
    have hz : ((2 * k : Nat) : ZMod 2) = 0 := by
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
    simp [hz, h0]
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    subst hk
    have ho : ((2 * k + 1 : Nat) : ZMod 2) = 1 := by
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    simp [ho, h1]

private theorem natToPoly_clMul (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    natToPoly (clMul a b) = natToPoly a * natToPoly b := by
  rw [natToPoly_eq_sum a 256 ha, natToPoly_eq_sum b 256 hb, Finset.sum_mul]
  simp only [Finset.mul_sum]
  have hProd : (∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
      (if a.testBit i = true then (Polynomial.X : Polynomial (ZMod 2)) ^ i else 0) *
      (if b.testBit j = true then Polynomial.X ^ j else 0)) =
      ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
        if a.testBit i = true ∧ b.testBit j = true then
          (Polynomial.X : Polynomial (ZMod 2)) ^ (i + j) else 0 := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases h1 : a.testBit i <;> by_cases h2 : b.testBit j <;>
      simp [h1, h2, pow_add]
  rw [hProd]
  ext k
  rw [natToPoly_coeff, clMul_testBit a b k ha hb, poly_finset_sum_coeff]
  have hInner : (∑ i ∈ Finset.range 256,
      (∑ j ∈ Finset.range 256,
        if a.testBit i = true ∧ b.testBit j = true then
          (Polynomial.X : Polynomial (ZMod 2)) ^ (i + j) else 0).coeff k) =
      ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
        (if a.testBit i = true ∧ b.testBit j = true then
          (Polynomial.X : Polynomial (ZMod 2)) ^ (i + j) else 0).coeff k := by
    apply Finset.sum_congr rfl; intro i _; exact poly_finset_sum_coeff _ _ k
  rw [hInner]
  have hCoeff : (∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
      (if a.testBit i = true ∧ b.testBit j = true then
        (Polynomial.X : Polynomial (ZMod 2)) ^ (i + j) else 0).coeff k) =
      ((polyCoeffSum a b k : Nat) : ZMod 2) := by
    unfold polyCoeffSum
    push_cast
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases h1 : i + j = k <;> by_cases h2 : a.testBit i <;> by_cases h3 : b.testBit j <;>
      simp [h1, h2, h3, Polynomial.coeff_X_pow, show k ≠ i + j ↔ ¬ i + j = k by omega]
  rw [hCoeff, natCast_zmod2]
  by_cases hk : k < 512
  · simp only [hk, true_and, decide_eq_true_eq]
  · have hS0 : polyCoeffSum a b k = 0 := by
      unfold polyCoeffSum
      apply Finset.sum_eq_zero; intro i hi
      apply Finset.sum_eq_zero; intro j hj
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      split_ifs with h
      · exfalso; omega
      · rfl
    simp [hk, hS0]

noncomputable def charPoly : Polynomial (ZMod 2) := Polynomial.X ^ 256 + natToPoly pLow

private theorem charPoly_monic : charPoly.Monic :=
  Polynomial.monic_X_pow_add (natToPoly_degree_lt pLow 256 pLow_lt)

private theorem charPoly_degree : charPoly.degree = (256 : WithBot ℕ) := by
  have hLt : (natToPoly pLow).degree < (Polynomial.X ^ 256 : Polynomial (ZMod 2)).degree := by
    rw [Polynomial.degree_X_pow]
    exact natToPoly_degree_lt pLow 256 pLow_lt
  unfold charPoly
  rw [Polynomial.degree_add_eq_left_of_degree_lt hLt, Polynomial.degree_X_pow]
  rfl

private theorem degree_mul_X_pow_lt {S : Polynomial (ZMod 2)} {m N : Nat}
    (h : (S * Polynomial.X ^ m).degree < ((N + m : Nat) : WithBot ℕ)) :
    S.degree < (N : WithBot ℕ) := by
  by_cases hS : S = 0
  · subst hS; simp
  · have hMul : (S * Polynomial.X ^ m).degree = S.degree + (m : WithBot ℕ) := by
      rw [Polynomial.degree_mul' (by simp [hS]), Polynomial.degree_X_pow]
    rw [hMul] at h
    rw [Polynomial.degree_eq_natDegree hS] at h ⊢
    norm_cast at h ⊢
    omega

private theorem modByMonic_mul_left (p q : Polynomial (ZMod 2)) :
    (p %ₘ charPoly * q) %ₘ charPoly = (p * q) %ₘ charPoly := by
  have hIdem : (p %ₘ charPoly) %ₘ charPoly = p %ₘ charPoly :=
    (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr
      (Polynomial.degree_modByMonic_lt _ charPoly_monic)
  rw [Polynomial.mul_modByMonic _ _ charPoly, hIdem, ← Polynomial.mul_modByMonic p q charPoly]

private theorem modByMonic_mul_right (p q : Polynomial (ZMod 2)) :
    (p * (q %ₘ charPoly)) %ₘ charPoly = (p * q) %ₘ charPoly := by
  have hIdem : (q %ₘ charPoly) %ₘ charPoly = q %ₘ charPoly :=
    (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr
      (Polynomial.degree_modByMonic_lt _ charPoly_monic)
  rw [Polynomial.mul_modByMonic _ _ charPoly, hIdem, ← Polynomial.mul_modByMonic p q charPoly]

private theorem add_charPoly_modByMonic (p : Polynomial (ZMod 2)) :
    (p + charPoly) %ₘ charPoly = p %ₘ charPoly := by
  rw [Polynomial.add_modByMonic, Polynomial.modByMonic_self charPoly_monic, add_zero]

private theorem withBot_add_lt {a b : WithBot ℕ} {m n : Nat}
    (ha : a < (m : WithBot ℕ)) (hb : b < (n : WithBot ℕ)) :
    a + b < ((m + n : Nat) : WithBot ℕ) := by
  cases a with
  | bot => simp
  | coe x =>
    cases b with
    | bot => simp
    | coe y =>
      have hx : x < m := Nat.cast_lt.mp ha
      have hy : y < n := Nat.cast_lt.mp hb
      change ((x + y : Nat) : WithBot ℕ) < ((m + n : Nat) : WithBot ℕ)
      exact Nat.cast_lt.mpr (Nat.add_lt_add hx hy)

private def barrettR0 : Nat :=
  (clMul barrettQ0 pLow ^^^ (barrettQ0 <<< 256)) ^^^ (1 <<< 511)

private theorem barrettR0_deg : (natToPoly barrettR0).degree < (256 : WithBot ℕ) :=
  natToPoly_degree_lt barrettR0 256 barrett_rem_bound

private theorem barrettR0_poly :
    natToPoly barrettR0 = natToPoly barrettQ0 * charPoly + Polynomial.X ^ 511 := by
  unfold barrettR0
  rw [natToPoly_xor, natToPoly_xor, natToPoly_clMul barrettQ0 pLow barrettQ0_lt pLow_lt,
    natToPoly_shiftLeft, natToPoly_shiftLeft, natToPoly_one, one_mul]
  unfold charPoly
  rw [mul_add, add_comm (natToPoly barrettQ0 * Polynomial.X ^ 256)]

private theorem barrett_alg {c M q R0 : Nat}
    (hcHiLt : c >>> 256 < 2 ^ 255) (hcLoLt : c &&& mask256 < 2 ^ 256)
    (hq : q = M >>> 255) (hqLt : q < 2 ^ 255) (hmLoLt : M &&& mask255 < 2 ^ 255)
    (hR0Deg : (natToPoly R0).degree < (256 : WithBot ℕ))
    (hR0Poly : natToPoly R0 = natToPoly barrettQ0 * charPoly + Polynomial.X ^ 511)
    (hMPoly : natToPoly M = natToPoly (c >>> 256) * natToPoly barrettQ0) :
    natToPoly ((c ^^^ clMul q pLow) &&& mask256) = natToPoly c %ₘ charPoly := by
  have hqLt256 : q < 2 ^ 256 := lt_trans hqLt (two_pow_lt_two_pow (by decide : 255 < 256))
  have hOutLt : (c ^^^ clMul q pLow) &&& mask256 < 2 ^ 256 := and_mask256_lt _
  have hMDecomp : natToPoly M = natToPoly q * Polynomial.X ^ 255 + natToPoly (M &&& mask255) := by
    rw [hq, mask255_def]
    exact natToPoly_shiftRight_add M 255
  have hCDecomp : natToPoly c = natToPoly (c >>> 256) * Polynomial.X ^ 256 +
      natToPoly (c &&& mask256) := by
    rw [mask256_def]
    exact natToPoly_shiftRight_add c 256
  let S : Polynomial (ZMod 2) :=
    natToPoly q * charPoly + natToPoly (c >>> 256) * Polynomial.X ^ 256
  have hSX : S * Polynomial.X ^ 255 =
      natToPoly (c >>> 256) * natToPoly R0 + natToPoly (M &&& mask255) * charPoly := by
    have hPow :
        (Polynomial.X : Polynomial (ZMod 2)) ^ 511 = Polynomial.X ^ 256 * Polynomial.X ^ 255 := by
      rw [← pow_add]
    have hZ1 := poly_add_self_zmod2 (natToPoly (M &&& mask255) * charPoly)
    calc S * Polynomial.X ^ 255
        = S * Polynomial.X ^ 255 +
            (natToPoly (M &&& mask255) * charPoly + natToPoly (M &&& mask255) * charPoly) := by
          rw [hZ1, add_zero]
      _ = (natToPoly q * Polynomial.X ^ 255 + natToPoly (M &&& mask255)) * charPoly +
            natToPoly (c >>> 256) * Polynomial.X ^ 511 +
            natToPoly (M &&& mask255) * charPoly := by
          dsimp only [S]; rw [hPow]; ring
      _ = natToPoly (c >>> 256) * (natToPoly barrettQ0 * charPoly + Polynomial.X ^ 511) +
            natToPoly (M &&& mask255) * charPoly := by
          rw [← hMDecomp, hMPoly]; ring
      _ = natToPoly (c >>> 256) * natToPoly R0 + natToPoly (M &&& mask255) * charPoly := by
          rw [← hR0Poly]
  have hDeg1 : (natToPoly (c >>> 256) * natToPoly R0).degree < (511 : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    exact withBot_add_lt (natToPoly_degree_lt _ 255 hcHiLt) hR0Deg
  have hDeg2 : (natToPoly (M &&& mask255) * charPoly).degree < (511 : WithBot ℕ) := by
    calc (natToPoly (M &&& mask255) * charPoly).degree
        ≤ (natToPoly (M &&& mask255)).degree + charPoly.degree := Polynomial.degree_mul_le _ _
      _ < (255 : WithBot ℕ) + (256 : WithBot ℕ) := by
          rw [charPoly_degree]
          exact WithBot.add_lt_add_right WithBot.coe_ne_bot (natToPoly_degree_lt _ 255 hmLoLt)
      _ = (511 : WithBot ℕ) := rfl
  have hSDeg : S.degree < (256 : WithBot ℕ) := by
    apply degree_mul_X_pow_lt (m := 255) (N := 256)
    rw [hSX]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hDeg1 hDeg2)
  let rem : Polynomial (ZMod 2) := S + natToPoly (c &&& mask256)
  have hRemDeg : rem.degree < charPoly.degree := by
    rw [charPoly_degree]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt hSDeg (natToPoly_degree_lt _ 256 hcLoLt))
  have hRemEq : rem = natToPoly q * charPoly + natToPoly c := by
    dsimp only [rem, S]
    rw [hCDecomp]
    ring
  have hDiv : rem + charPoly * natToPoly q = natToPoly c := by
    rw [hRemEq]
    have hZ := poly_add_self_zmod2 (charPoly * natToPoly q)
    calc (natToPoly q * charPoly + natToPoly c) + charPoly * natToPoly q
        = natToPoly c + (charPoly * natToPoly q + charPoly * natToPoly q) := by ring
      _ = natToPoly c := by rw [hZ, add_zero]
  have hMod : natToPoly c %ₘ charPoly = rem :=
    (Polynomial.div_modByMonic_unique (natToPoly q) rem charPoly_monic ⟨hDiv, hRemDeg⟩).2
  rw [hMod]
  ext k
  by_cases hk : k < 256
  · have hMaskBit : ∀ u, ((u &&& mask256).testBit k) = u.testBit k := fun u => by
      rw [and_mask256_testBit, decide_eq_true hk, Bool.true_and]
    rw [natToPoly_coeff, hMaskBit]
    have hXorBit : natToPoly (c ^^^ clMul q pLow) =
        natToPoly c + natToPoly q * natToPoly pLow := by
      rw [natToPoly_xor, natToPoly_clMul q pLow hqLt256 pLow_lt]
    have hRemSum : rem = (natToPoly c + natToPoly q * natToPoly pLow) +
        natToPoly q * Polynomial.X ^ 256 := by
      rw [hRemEq]; unfold charPoly; ring
    have hX256 : (natToPoly q * Polynomial.X ^ 256).coeff k = 0 := by
      rw [Polynomial.coeff_mul_X_pow']
      simp [show ¬ 256 ≤ k by omega]
    rw [hRemSum, Polynomial.coeff_add, hX256, add_zero, ← hXorBit, natToPoly_coeff]
  · have hRemZero : rem.coeff k = 0 := by
      rw [charPoly_degree] at hRemDeg
      exact (Polynomial.degree_lt_iff_coeff_zero _ 256).mp hRemDeg k (by omega)
    have hOutZero : (natToPoly ((c ^^^ clMul q pLow) &&& mask256)).coeff k = 0 := by
      have hLtK : (natToPoly ((c ^^^ clMul q pLow) &&& mask256)).degree < (256 : WithBot ℕ) :=
        natToPoly_degree_lt _ 256 hOutLt
      exact (Polynomial.degree_lt_iff_coeff_zero _ 256).mp hLtK k (by omega)
    rw [hRemZero, hOutZero]

set_option exponentiation.threshold 1024 in
private theorem natToPoly_polyMul {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    polyMul a b < 2 ^ 256 ∧
      natToPoly (polyMul a b) = (natToPoly a * natToPoly b) %ₘ charPoly := by
  unfold polyMul
  dsimp only
  set c := clMul a b
  have hcLt : c < 2 ^ 511 :=
    clMul_lt_pow (by decide) (by decide) (le_refl 256) (le_refl 256) rfl ha hb
  have hcHiLt : c >>> 256 < 2 ^ 255 := by
    have h511 : (2 : Nat) ^ 256 * 2 ^ 255 = 2 ^ 511 := by
      have h : 256 + 255 = 511 := by decide
      rw [← Nat.pow_add, h]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [h511]; exact hcLt)
  have hMLt : clMul (c >>> 256) barrettQ0 < 2 ^ 510 :=
    clMul_lt_pow (by decide) (by decide) (by decide) (le_refl 256) rfl hcHiLt barrettQ0_lt
  set M := clMul (c >>> 256) barrettQ0
  set q := M >>> 255
  have hqLt : q < 2 ^ 255 := by
    have h510 : (2 : Nat) ^ 255 * 2 ^ 255 = 2 ^ 510 := by
      have h : 255 + 255 = 510 := by decide
      rw [← Nat.pow_add, h]
    simp only [q, Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [h510]; exact hMLt)
  have hMPoly : natToPoly M = natToPoly (c >>> 256) * natToPoly barrettQ0 :=
    natToPoly_clMul (c >>> 256) barrettQ0
      (lt_trans hcHiLt (two_pow_lt_two_pow (by decide : 255 < 256))) barrettQ0_lt
  refine ⟨and_mask256_lt _, ?_⟩
  rw [← natToPoly_clMul a b ha hb]
  exact barrett_alg hcHiLt (and_mask256_lt c) rfl hqLt (and_mask255_lt M) barrettR0_deg
    barrettR0_poly hMPoly

private theorem poly_pow_modByMonic_idem (f : Polynomial (ZMod 2)) (m : Nat) :
    (f %ₘ charPoly) ^ m %ₘ charPoly = f ^ m %ₘ charPoly := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, modByMonic_mul_right, ← modByMonic_mul_left, ih, modByMonic_mul_left]

private theorem natToPoly_polyPowGo :
    ∀ (fuel a e acc : Nat), e < 2 ^ fuel → a < 2 ^ 256 → acc < 2 ^ 256 →
      polyPowGo fuel a e acc < 2 ^ 256 ∧
        natToPoly (polyPowGo fuel a e acc) =
          (natToPoly acc * natToPoly a ^ e) %ₘ charPoly
  | 0, a, e, acc, he, _, hacc => by
    have he0 : e = 0 := by omega
    subst he0
    simp only [polyPowGo, pow_zero, mul_one]
    have hDegAcc : (natToPoly acc).degree < charPoly.degree := by
      rw [charPoly_degree]
      exact natToPoly_degree_lt acc 256 hacc
    have hMod := (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr hDegAcc
    exact ⟨hacc, hMod.symm⟩
  | fuel + 1, a, e, acc, he, ha, hacc => by
    rw [polyPowGo]
    by_cases hE0 : e = 0
    · subst hE0
      simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, pow_zero, mul_one]
      have hDegAcc : (natToPoly acc).degree < charPoly.degree := by
        rw [charPoly_degree]
        exact natToPoly_degree_lt acc 256 hacc
      have hMod := (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr hDegAcc
      exact ⟨hacc, hMod.symm⟩
    · by_cases hAcc0 : acc = 0
      · subst hAcc0
        simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte, natToPoly_zero, zero_mul,
          Polynomial.zero_modByMonic]
        exact ⟨pow256_pos, trivial⟩
      · have hE0B : (e == 0) = false := beq_false_of_ne hE0
        have hAcc0B : (acc == 0) = false := beq_false_of_ne hAcc0
        simp only [hE0B, hAcc0B, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        by_cases hA0 : a = 0
        · subst hA0
          simp only [beq_self_eq_true, ↓reduceIte, natToPoly_zero, zero_pow hE0, mul_zero,
            Polynomial.zero_modByMonic]
          exact ⟨pow256_pos, trivial⟩
        · have hA0B : (a == 0) = false := beq_false_of_ne hA0
          simp only [hA0B, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨haSqLt, haSqPoly⟩ := natToPoly_polyMul ha ha
          have hR1 : e >>> 1 = e / 2 := by rw [Nat.shiftRight_eq_div_pow]
          have hEHalfLt : e >>> 1 < 2 ^ fuel := by
            rw [hR1]
            exact Nat.div_lt_of_lt_mul
              (lt_of_lt_of_le he (by rw [Nat.pow_succ, Nat.mul_comm]))
          have hAnd1 : e &&& 1 = e % 2 := Nat.and_one_is_mod e
          by_cases hOdd : (e &&& 1 == 1) = true
          · simp only [hOdd, ↓reduceIte]
            obtain ⟨hAcc1Lt, hAcc1Poly⟩ := natToPoly_polyMul hacc ha
            obtain ⟨hResLt, hResPoly⟩ := natToPoly_polyPowGo fuel (polyMul a a) (e >>> 1)
              (polyMul acc a) hEHalfLt haSqLt hAcc1Lt
            refine ⟨hResLt, hResPoly.trans ?_⟩
            rw [hAcc1Poly, haSqPoly, modByMonic_mul_left, ← modByMonic_mul_right,
              poly_pow_modByMonic_idem, modByMonic_mul_right]
            have hEMod : e % 2 = 1 := by have := eq_of_beq hOdd; omega
            have heEq : e = 2 * (e >>> 1) + 1 := by omega
            have hExpEq : (natToPoly acc * natToPoly a) * (natToPoly a * natToPoly a) ^ (e >>> 1) =
                natToPoly acc * natToPoly a ^ e := by
              conv_rhs => rw [heEq, pow_add, pow_mul, pow_one, sq]
              ring
            rw [hExpEq]
          · have hOddF : (e &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
            simp only [hOddF, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨hResLt, hResPoly⟩ := natToPoly_polyPowGo fuel (polyMul a a) (e >>> 1)
              acc hEHalfLt haSqLt hacc
            refine ⟨hResLt, hResPoly.trans ?_⟩
            rw [haSqPoly, ← modByMonic_mul_right, poly_pow_modByMonic_idem, modByMonic_mul_right]
            have hEMod : e % 2 = 0 := by
              have hModLt := Nat.mod_lt e (by decide : 0 < 2)
              have hNe : e % 2 ≠ 1 := fun h => hOdd (by rw [hAnd1, h]; rfl)
              omega
            have heEq : e = 2 * (e >>> 1) := by omega
            have hExpEq : natToPoly acc * (natToPoly a * natToPoly a) ^ (e >>> 1) =
                natToPoly acc * natToPoly a ^ e := by
              conv_rhs => rw [heEq, pow_mul, sq]
            rw [hExpEq]

private theorem natToPoly_polyPow (a e : Nat) (he : e < 2 ^ 257) (ha : a < 2 ^ 256) :
    polyPow a e < 2 ^ 256 ∧ natToPoly (polyPow a e) = (natToPoly a ^ e) %ₘ charPoly := by
  have h := natToPoly_polyPowGo 257 a e 1 he ha one_lt_pow256
  simpa [polyPow, natToPoly_one] using h

private def powModGo (p : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, e, acc =>
    if e == 0 then acc
    else
      let acc1 := if e &&& 1 == 1 then (acc * a) % p else acc
      powModGo p fuel ((a * a) % p) (e >>> 1) acc1

private def powMod (a e p : Nat) : Nat := powModGo p 75 (a % p) e (1 % p)

private theorem powModGo_spec (p : Nat) (hp : 1 < p) :
    ∀ fuel a e acc : Nat, e < 2 ^ fuel → acc < p →
      powModGo p fuel a e acc < p ∧
        ((powModGo p fuel a e acc : Nat) : ZMod p) = (acc : ZMod p) * (a : ZMod p) ^ e
  | 0, _, e, acc, he, hacc => by
    have he0 : e = 0 := by omega
    subst he0
    simp [powModGo, hacc]
  | fuel + 1, a, e, acc, he, hacc => by
    rw [powModGo]
    by_cases hE0 : e = 0
    · subst hE0; simp [hacc]
    · have hE0B : (e == 0) = false := beq_false_of_ne hE0
      simp only [hE0B, Bool.false_eq_true, ↓reduceIte]
      have hR1 : e >>> 1 = e / 2 := by rw [Nat.shiftRight_eq_div_pow]
      have hEHalf : e >>> 1 < 2 ^ fuel := by
        rw [hR1]
        exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le he (by rw [Nat.pow_succ, Nat.mul_comm]))
      have hp0 : 0 < p := by omega
      have hAnd1 : e &&& 1 = e % 2 := Nat.and_one_is_mod e
      by_cases hOdd : (e &&& 1 == 1) = true
      · simp only [hOdd, ↓reduceIte]
        have hAcc1Lt : (acc * a) % p < p := Nat.mod_lt _ hp0
        obtain ⟨hRLt, hRCast⟩ :=
          powModGo_spec p hp fuel ((a * a) % p) (e >>> 1) ((acc * a) % p) hEHalf hAcc1Lt
        refine ⟨hRLt, hRCast.trans ?_⟩
        rw [ZMod.natCast_mod, ZMod.natCast_mod]
        have hEMod : e % 2 = 1 := by have := eq_of_beq hOdd; omega
        have heEq : e = 2 * (e >>> 1) + 1 := by omega
        push_cast
        conv_rhs => rw [heEq, pow_add, pow_mul, sq]
        ring
      · have hOddF : (e &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
        simp only [hOddF, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hRLt, hRCast⟩ := powModGo_spec p hp fuel ((a * a) % p) (e >>> 1) acc
          hEHalf hacc
        refine ⟨hRLt, hRCast.trans ?_⟩
        rw [ZMod.natCast_mod]
        have hEMod : e % 2 = 0 := by
          have hModLt := Nat.mod_lt e (by decide : 0 < 2)
          have hNe : e % 2 ≠ 1 := fun h => hOdd (by rw [hAnd1, h]; rfl)
          omega
        have heEq : e = 2 * (e >>> 1) := by omega
        push_cast
        conv_rhs => rw [heEq, pow_mul, sq]

private theorem prime_dvd_factor_prod (q : Nat) (hq : q.Prime) :
    ∀ factors : List (Nat × Nat), (∀ pq ∈ factors, pq.1.Prime) →
      q ∣ (factors.map fun pq => pq.1 ^ pq.2).prod →
      ∃ pq ∈ factors, q = pq.1
  | [], _, hdvd => by
    simp only [List.map_nil, List.prod_nil] at hdvd
    exact absurd hdvd hq.not_dvd_one
  | pq :: rest, hPrimes, hdvd => by
    simp only [List.map_cons, List.prod_cons] at hdvd
    rcases hq.dvd_mul.mp hdvd with hHead | hTail
    · rcases (hPrimes pq List.mem_cons_self).eq_one_or_self_of_dvd q
          (hq.dvd_of_dvd_pow hHead) with h1 | hEq
      · exact absurd h1 hq.ne_one
      · exact ⟨pq, List.mem_cons_self, hEq⟩
    · obtain ⟨w, hw, hEq⟩ := prime_dvd_factor_prod q hq rest
        (fun x hx => hPrimes x (List.mem_cons_of_mem _ hx)) hTail
      exact ⟨w, List.mem_cons_of_mem _ hw, hEq⟩

private theorem prime_of_lucas (p a : Nat) (factors : List (Nat × Nat))
    (hp1 : 1 < p) (hBound : p - 1 < 2 ^ 75)
    (hProd : (factors.map fun pq => pq.1 ^ pq.2).prod = p - 1)
    (hPrimes : ∀ pq ∈ factors, pq.1.Prime)
    (hTop : powMod a (p - 1) p = 1)
    (hDivs : factors.all (fun pq => powMod a ((p - 1) / pq.1) p != 1) = true) :
    p.Prime := by
  have : NeZero p := ⟨by omega⟩
  apply lucas_primality p (a : ZMod p)
  · have hSpec := (powModGo_spec p hp1 75 (a % p) (p - 1) (1 % p) hBound
      (Nat.mod_lt _ (by omega))).2
    change ((powMod a (p - 1) p : Nat) : ZMod p) = _ at hSpec
    rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_one, one_mul, hTop] at hSpec
    simpa using hSpec.symm
  · intro q hq hqDvd
    rw [← hProd] at hqDvd
    obtain ⟨pq, hpqMem, hqEq⟩ := prime_dvd_factor_prod q hq factors hPrimes hqDvd
    subst hqEq
    have hNeOne : powMod a ((p - 1) / pq.1) p ≠ 1 := by
      have hB := (List.all_eq_true.mp hDivs) pq hpqMem
      exact bne_iff_ne.mp hB
    have hSub : (p - 1) / pq.1 < 2 ^ 75 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hBound
    have hRL1 := powModGo_spec p hp1 75 (a % p) ((p - 1) / pq.1) (1 % p) hSub
      (Nat.mod_lt _ (by omega))
    change powMod a ((p - 1) / pq.1) p < p ∧
      ((powMod a ((p - 1) / pq.1) p : Nat) : ZMod p) =
        ((1 % p : Nat) : ZMod p) * ((a % p : Nat) : ZMod p) ^ ((p - 1) / pq.1) at hRL1
    have : Fact (1 < p) := ⟨hp1⟩
    rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_one, one_mul] at hRL1
    rw [← hRL1.2]
    intro hCastOne
    have hVal := congrArg ZMod.val hCastOne
    rw [ZMod.val_natCast, ZMod.val_one p, Nat.mod_eq_of_lt hRL1.1] at hVal
    exact hNeOne hVal
private theorem prime_2 : Nat.Prime 2 := by norm_num
private theorem prime_3 : Nat.Prime 3 := by norm_num
private theorem prime_5 : Nat.Prime 5 := by norm_num
private theorem prime_7 : Nat.Prime 7 := by norm_num
private theorem prime_11 : Nat.Prime 11 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num
private theorem prime_47 : Nat.Prime 47 := by norm_num
private theorem prime_71 : Nat.Prime 71 := by norm_num
private theorem prime_139 : Nat.Prime 139 := by norm_num
private theorem prime_181 : Nat.Prime 181 := by norm_num
private theorem prime_257 : Nat.Prime 257 := by norm_num
private theorem prime_347 : Nat.Prime 347 := by norm_num
private theorem prime_367 : Nat.Prime 367 := by norm_num
private theorem prime_373 : Nat.Prime 373 := by norm_num
private theorem prime_449 : Nat.Prime 449 := by norm_num
private theorem prime_641 : Nat.Prime 641 := by norm_num
private theorem prime_727 : Nat.Prime 727 := by norm_num
private theorem prime_823 : Nat.Prime 823 := by norm_num
set_option maxRecDepth 8192 in
private theorem prime_1783 : Nat.Prime 1783 := by
  refine prime_of_lucas 1783 10
    [(2, 1), (3, 4), (11, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_11

set_option maxRecDepth 8192 in
private theorem prime_2203 : Nat.Prime 2203 := by
  refine prime_of_lucas 2203 5
    [(2, 1), (3, 1), (367, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_367

set_option maxRecDepth 8192 in
private theorem prime_12497 : Nat.Prime 12497 := by
  refine prime_of_lucas 12497 3
    [(2, 4), (11, 1), (71, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_11
  · rw [h2]; exact prime_71

set_option maxRecDepth 8192 in
private theorem prime_16657 : Nat.Prime 16657 := by
  refine prime_of_lucas 16657 5
    [(2, 4), (3, 1), (347, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_347

set_option maxRecDepth 8192 in
private theorem prime_17449 : Nat.Prime 17449 := by
  refine prime_of_lucas 17449 14
    [(2, 3), (3, 1), (727, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_727

set_option maxRecDepth 8192 in
private theorem prime_52673 : Nat.Prime 52673 := by
  refine prime_of_lucas 52673 3
    [(2, 6), (823, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_823

set_option maxRecDepth 8192 in
private theorem prime_65537 : Nat.Prime 65537 := by
  refine prime_of_lucas 65537 3
    [(2, 16)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rw [hpq]; exact prime_2

set_option maxRecDepth 8192 in
private theorem prime_166571 : Nat.Prime 166571 := by
  refine prime_of_lucas 166571 2
    [(2, 1), (5, 1), (16657, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_5
  · rw [h2]; exact prime_16657

set_option maxRecDepth 8192 in
private theorem prime_274177 : Nat.Prime 274177 := by
  refine prime_of_lucas 274177 5
    [(2, 8), (3, 2), (7, 1), (17, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_7
  · rw [h3]; exact prime_17

set_option maxRecDepth 8192 in
private theorem prime_1896229 : Nat.Prime 1896229 := by
  refine prime_of_lucas 1896229 2
    [(2, 2), (3, 2), (52673, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_52673

set_option maxRecDepth 8192 in
private theorem prime_2998279 : Nat.Prime 2998279 := by
  refine prime_of_lucas 2998279 3
    [(2, 1), (3, 2), (166571, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_166571

set_option maxRecDepth 8192 in
private theorem prime_6700417 : Nat.Prime 6700417 := by
  refine prime_of_lucas 6700417 5
    [(2, 7), (3, 1), (17449, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_17449

set_option maxRecDepth 8192 in
private theorem prime_6939437 : Nat.Prime 6939437 := by
  refine prime_of_lucas 6939437 2
    [(2, 2), (7, 1), (139, 1), (1783, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_7
  · rw [h2]; exact prime_139
  · rw [h3]; exact prime_1783

set_option maxRecDepth 8192 in
private theorem prime_55515497 : Nat.Prime 55515497 := by
  refine prime_of_lucas 55515497 3
    [(2, 3), (6939437, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_6939437

set_option maxRecDepth 8192 in
private theorem prime_18533742247 : Nat.Prime 18533742247 := by
  refine prime_of_lucas 18533742247 6
    [(2, 1), (3, 3), (181, 1), (1896229, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_181
  · rw [h3]; exact prime_1896229

set_option maxRecDepth 8192 in
private theorem prime_733803839347 : Nat.Prime 733803839347 := by
  refine prime_of_lucas 733803839347 2
    [(2, 1), (3, 1), (2203, 1), (55515497, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_2203
  · rw [h3]; exact prime_55515497

set_option maxRecDepth 8192 in
private theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine prime_of_lucas 67280421310721 3
    [(2, 8), (5, 1), (47, 1), (373, 1), (2998279, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3 | h4
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_5
  · rw [h2]; exact prime_47
  · rw [h3]; exact prime_373
  · rw [h4]; exact prime_2998279

set_option maxRecDepth 8192 in
private theorem prime_116503103764643 : Nat.Prime 116503103764643 := by
  refine prime_of_lucas 116503103764643 2
    [(2, 1), (7, 1), (449, 1), (18533742247, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_7
  · rw [h2]; exact prime_449
  · rw [h3]; exact prime_18533742247

set_option maxRecDepth 8192 in
private theorem prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  refine prime_of_lucas 59649589127497217 3
    [(2, 9), (116503103764643, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_116503103764643

set_option maxRecDepth 8192 in
private theorem prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  refine prime_of_lucas 5704689200685129054721 21
    [(2, 9), (3, 5), (5, 1), (12497, 1), (733803839347, 1)]
    (by decide) (by decide) (by decide) (fun pq hpq => ?_) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpq
  rcases hpq with h0 | h1 | h2 | h3 | h4
  · rw [h0]; exact prime_2
  · rw [h1]; exact prime_3
  · rw [h2]; exact prime_5
  · rw [h3]; exact prime_12497
  · rw [h4]; exact prime_733803839347

private theorem primeFactors256_all_prime :
    ∀ q ∈ primeFactors256, Nat.Prime q := by
  intro q hq
  simp only [primeFactors256, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_3
  · exact prime_5
  · exact prime_17
  · exact prime_257
  · exact prime_641
  · exact prime_65537
  · exact prime_274177
  · exact prime_6700417
  · exact prime_67280421310721
  · exact prime_59649589127497217
  · exact prime_5704689200685129054721

private theorem nat_div_mul_assoc {a b q : Nat} (hq : q ∣ a) : (a * b) / q = (a / q) * b := by
  rcases hq with ⟨k, rfl⟩
  by_cases hq0 : q = 0
  · subst hq0; simp
  · rw [mul_assoc, Nat.mul_div_right _ (Nat.pos_of_ne_zero hq0),
      Nat.mul_div_right _ (Nat.pos_of_ne_zero hq0)]

private theorem nat_mul_div_assoc {a b q : Nat} (hq : q ∣ b) : (a * b) / q = a * (b / q) := by
  rw [mul_comm, nat_div_mul_assoc hq, mul_comm]

private theorem checkTree_sound :
    ∀ (fuel : Nat) (ps : List Nat) (g e : Nat),
      g < 2 ^ 256 → ps.prod ≤ 2 ^ 256 - 1 → (∀ q ∈ ps, 0 < q) →
      natToPoly g = (Polynomial.X ^ e) %ₘ charPoly →
      checkTree g fuel ps = true →
      ∀ q ∈ ps, (Polynomial.X ^ (e * (ps.prod / q))) %ₘ charPoly ≠ 1
  | 0, _, _, _, _, _, _, _, h, _, _ => by simp [checkTree] at h
  | _ + 1, [], _, _, _, _, _, _, _, _, hq => by simp at hq
  | _ + 1, [q0], g, e, _, _, hPos, hg, hChk, q, hq => by
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [List.prod_singleton, Nat.div_self (hPos q List.mem_cons_self), mul_one]
    have hNe1 : g ≠ 1 := by
      have hB : (g != 1) = true := hChk
      exact bne_iff_ne.mp hB
    rw [← hg]
    intro hOne
    exact hNe1 (natToPoly_inj (hOne.trans natToPoly_one.symm))
  | fuel + 1, p1 :: p2 :: rest, g, e, hgLt, hProd, hPos, hg, hChk, q, hq => by
    set ps := p1 :: p2 :: rest
    set half := ps.length / 2
    set left := ps.take half
    set right := ps.drop half
    change checkTree (polyPow g right.prod) fuel left &&
      checkTree (polyPow g left.prod) fuel right = true at hChk
    have hLR := Bool.and_eq_true_iff.mp hChk
    have hProdEq : left.prod * right.prod = ps.prod := by
      rw [← List.prod_append, List.take_append_drop]
    have hLeftPos : ∀ x ∈ left, 0 < x := fun x hx => hPos x (List.mem_of_mem_take hx)
    have hRightPos : ∀ x ∈ right, 0 < x := fun x hx => hPos x (List.mem_of_mem_drop hx)
    have hLeftProdPos : 0 < left.prod := List.prod_pos hLeftPos
    have hRightProdPos : 0 < right.prod := List.prod_pos hRightPos
    have hLeftProdLe : left.prod ≤ ps.prod := by
      rw [← hProdEq]; exact Nat.le_mul_of_pos_right _ hRightProdPos
    have hRightProdLe : right.prod ≤ ps.prod := by
      rw [← hProdEq]; exact Nat.le_mul_of_pos_left _ hLeftProdPos
    have h256Lt257 : 2 ^ 256 - 1 < 2 ^ 257 :=
      lt_trans pow256_sub_one_lt pow256_lt_pow257
    have hLeftLt257 : left.prod < 2 ^ 257 :=
      lt_of_le_of_lt (le_trans hLeftProdLe hProd) h256Lt257
    have hRightLt257 : right.prod < 2 ^ 257 :=
      lt_of_le_of_lt (le_trans hRightProdLe hProd) h256Lt257
    have hSplit := List.take_append_drop half ps
    have hMem : q ∈ left ∨ q ∈ right := by
      rw [← List.mem_append, hSplit]; exact hq
    rcases hMem with hL | hR
    · obtain ⟨hgLLt, hgLPoly⟩ := natToPoly_polyPow g right.prod hRightLt257 hgLt
      have hgLExact : natToPoly (polyPow g right.prod) =
          (Polynomial.X ^ (e * right.prod)) %ₘ charPoly := by
        rw [hgLPoly, hg, poly_pow_modByMonic_idem, ← pow_mul]
      have hIH := checkTree_sound fuel left (polyPow g right.prod) (e * right.prod)
        hgLLt (le_trans hLeftProdLe hProd) hLeftPos hgLExact hLR.1 q hL
      have hDvd : q ∣ left.prod := List.dvd_prod hL
      have hExp : e * (ps.prod / q) = e * right.prod * (left.prod / q) := by
        rw [← hProdEq, nat_div_mul_assoc hDvd]; ring
      rw [hExp]
      exact hIH
    · obtain ⟨hgRLt, hgRPoly⟩ := natToPoly_polyPow g left.prod hLeftLt257 hgLt
      have hgRExact : natToPoly (polyPow g left.prod) =
          (Polynomial.X ^ (e * left.prod)) %ₘ charPoly := by
        rw [hgRPoly, hg, poly_pow_modByMonic_idem, ← pow_mul]
      have hIH := checkTree_sound fuel right (polyPow g left.prod) (e * left.prod)
        hgRLt (le_trans hRightProdLe hProd) hRightPos hgRExact hLR.2 q hR
      have hDvd : q ∣ right.prod := List.dvd_prod hR
      have hExp : e * (ps.prod / q) = e * left.prod * (right.prod / q) := by
        rw [← hProdEq, nat_mul_div_assoc hDvd]; ring
      rw [hExp]
      exact hIH

private theorem prime_dvd_list_prod (q : Nat) (hq : q.Prime) :
    ∀ xs : List Nat, (∀ x ∈ xs, Nat.Prime x) → q ∣ xs.prod → q ∈ xs
  | [], _, hdvd => by simp only [List.prod_nil] at hdvd; exact absurd hdvd hq.not_dvd_one
  | x :: xs, hPrimes, hdvd => by
    simp only [List.prod_cons] at hdvd
    rcases hq.dvd_mul.mp hdvd with hHead | hTail
    · rcases (hPrimes x List.mem_cons_self).eq_one_or_self_of_dvd q hHead with h1 | hEq
      · exact absurd h1 hq.ne_one
      · exact hEq ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (prime_dvd_list_prod q hq xs (fun y hy => hPrimes y (List.mem_cons_of_mem _ hy)) hTail)

private theorem x_pow_period_mod :
    (Polynomial.X ^ (2 ^ 256 - 1)) %ₘ charPoly = 1 := by
  have hN257 : 2 ^ 256 - 1 < 2 ^ 257 := lt_trans pow256_sub_one_lt pow256_lt_pow257
  have hP := (natToPoly_polyPow 2 (2 ^ 256 - 1) hN257 two_lt_pow256).2
  rw [pow_period_one, natToPoly_one, natToPoly_two] at hP
  exact hP.symm

private theorem x_pow_prime_quot_ne_one {q : Nat} (hq : q.Prime) (hdvd : q ∣ 2 ^ 256 - 1) :
    (Polynomial.X ^ ((2 ^ 256 - 1) / q)) %ₘ charPoly ≠ 1 := by
  have hdvd' : q ∣ primeFactors256.prod := primeFactors256_prod.symm ▸ hdvd
  have hQMem : q ∈ primeFactors256 :=
    prime_dvd_list_prod q hq primeFactors256 primeFactors256_all_prime hdvd'
  have hMod2 : natToPoly 2 = (Polynomial.X ^ 1) %ₘ charPoly := by
    rw [natToPoly_two, pow_one, (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr (by
      rw [charPoly_degree, Polynomial.degree_X]; decide)]
  have hAllOne : ∀ p ∈ primeFactors256, 0 < p :=
    fun p hp => (primeFactors256_all_prime p hp).pos
  have hChk := checkTree_sound 6 primeFactors256 2 1 two_lt_pow256
    (by rw [primeFactors256_prod]) hAllOne hMod2 tree_check q hQMem
  simpa [primeFactors256_prod] using hChk

private theorem pow_gcd_mod_aux :
    ∀ (s a b : Nat), a + b ≤ s →
      (Polynomial.X ^ a) %ₘ charPoly = 1 → (Polynomial.X ^ b) %ₘ charPoly = 1 →
      (Polynomial.X ^ Nat.gcd a b) %ₘ charPoly = 1
  | 0, a, b, hs, ha, _ => by
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0 hb0
    simpa using ha
  | s + 1, a, b, hs, ha, hb => by
    by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · by_cases hb0 : b = 0
      · subst hb0; simpa using ha
      · by_cases hle : a ≤ b
        · have hSub : (Polynomial.X ^ (b - a)) %ₘ charPoly = 1 := by
            have hModId : ((Polynomial.X ^ (b - a)) %ₘ charPoly) %ₘ charPoly =
                (Polynomial.X ^ (b - a)) %ₘ charPoly :=
              (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr
                (Polynomial.degree_modByMonic_lt _ charPoly_monic)
            calc (Polynomial.X ^ (b - a)) %ₘ charPoly
                = ((Polynomial.X ^ (b - a)) %ₘ charPoly * 1) %ₘ charPoly := by
                  rw [mul_one, hModId]
              _ = ((Polynomial.X ^ (b - a)) %ₘ charPoly * (Polynomial.X ^ a %ₘ charPoly)) %ₘ
                    charPoly := by rw [ha]
              _ = (Polynomial.X ^ (b - a) * Polynomial.X ^ a) %ₘ charPoly :=
                  (Polynomial.mul_modByMonic _ _ charPoly).symm
              _ = (Polynomial.X ^ b) %ₘ charPoly := by
                  rw [← pow_add, Nat.sub_add_cancel hle]
              _ = 1 := hb
          have hEqGcd : Nat.gcd a b = Nat.gcd a (b - a) := by
            rw [Nat.gcd_comm, Nat.gcd_sub_self_right hle, Nat.gcd_comm]
          rw [hEqGcd]
          exact pow_gcd_mod_aux s a (b - a) (by omega) ha hSub
        · have hlt : b ≤ a := by omega
          have hSub : (Polynomial.X ^ (a - b)) %ₘ charPoly = 1 := by
            have hModId : ((Polynomial.X ^ (a - b)) %ₘ charPoly) %ₘ charPoly =
                (Polynomial.X ^ (a - b)) %ₘ charPoly :=
              (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr
                (Polynomial.degree_modByMonic_lt _ charPoly_monic)
            calc (Polynomial.X ^ (a - b)) %ₘ charPoly
                = ((Polynomial.X ^ (a - b)) %ₘ charPoly * 1) %ₘ charPoly := by
                  rw [mul_one, hModId]
              _ = ((Polynomial.X ^ (a - b)) %ₘ charPoly * (Polynomial.X ^ b %ₘ charPoly)) %ₘ
                    charPoly := by rw [hb]
              _ = (Polynomial.X ^ (a - b) * Polynomial.X ^ b) %ₘ charPoly :=
                  (Polynomial.mul_modByMonic _ _ charPoly).symm
              _ = (Polynomial.X ^ a) %ₘ charPoly := by
                  rw [← pow_add, Nat.sub_add_cancel hlt]
              _ = 1 := ha
          have hEqGcd : Nat.gcd a b = Nat.gcd (a - b) b := (Nat.gcd_sub_self_left hlt).symm
          rw [hEqGcd]
          exact pow_gcd_mod_aux s (a - b) b (by omega) hSub hb

private theorem x_pow_mod_one_eq_zero {m : Nat} (hmLt : m < 2 ^ 256 - 1)
    (hm : (Polynomial.X ^ m) %ₘ charPoly = 1) : m = 0 := by
  by_contra hmPos
  set N := 2 ^ 256 - 1
  set d := Nat.gcd m N
  have hdDvdM : d ∣ m := Nat.gcd_dvd_left m N
  have hdDvdN : d ∣ N := Nat.gcd_dvd_right m N
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hmPos)
  have hdLe : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hmPos) hdDvdM
  have hdLtN : d < N := lt_of_le_of_lt hdLe hmLt
  set K := N / d
  have hNK : N = d * K := (Nat.mul_div_cancel' hdDvdN).symm
  have hKLt : 1 < K := by
    by_contra hLe1
    have hKLe : K ≤ 1 := Nat.le_of_not_lt hLe1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hKLe with hK0 | hK1
    · rw [hK0, mul_zero] at hNK
      exact absurd hNK (Nat.ne_of_gt pow256_sub_one_pos)
    · rw [hK1, mul_one] at hNK
      exact hdLtN.ne hNK.symm
  set q := Nat.minFac K
  have hqPrime : q.Prime := Nat.minFac_prime (by omega)
  have hqDvdK : q ∣ K := Nat.minFac_dvd K
  have hqDvdN : q ∣ N := hNK ▸ dvd_mul_of_dvd_right hqDvdK d
  obtain ⟨M, hKM⟩ := hqDvdK
  have hQuot : N / q = d * M := by
    have hEq : N = q * (d * M) := by rw [hNK, hKM]; ring
    rw [hEq, Nat.mul_div_right _ hqPrime.pos]
  have hGcdMod : (Polynomial.X ^ d) %ₘ charPoly = 1 :=
    pow_gcd_mod_aux (m + N) m N (le_refl _) hm x_pow_period_mod
  have hQuotOne : (Polynomial.X ^ (N / q)) %ₘ charPoly = 1 := by
    rw [hQuot, pow_mul, ← poly_pow_modByMonic_idem, hGcdMod, one_pow]
    exact (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr (by
      rw [charPoly_degree, Polynomial.degree_one]; decide)
  exact x_pow_prime_quot_ne_one hqPrime hqDvdN hQuotOne

private theorem x_pow_mod_inj {i j : Nat} (hi : i < 2 ^ 256 - 1) (hj : j < 2 ^ 256 - 1)
    (hEq : (Polynomial.X ^ i) %ₘ charPoly = (Polynomial.X ^ j) %ₘ charPoly) : i = j := by
  set N := 2 ^ 256 - 1
  wlog hij : i ≤ j generalizing i j
  · exact (this hEq.symm hj hi (by omega)).symm
  set k := j - i
  have hkLt : k < N := by omega
  have hkMod : (Polynomial.X ^ k) %ₘ charPoly = 1 := by
    have hModId : ((Polynomial.X ^ k) %ₘ charPoly) %ₘ charPoly =
        (Polynomial.X ^ k) %ₘ charPoly :=
      (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr
        (Polynomial.degree_modByMonic_lt _ charPoly_monic)
    calc (Polynomial.X ^ k) %ₘ charPoly
        = (1 * ((Polynomial.X ^ k) %ₘ charPoly)) %ₘ charPoly := by
          rw [one_mul, hModId]
      _ = ((Polynomial.X ^ N %ₘ charPoly) * (Polynomial.X ^ k %ₘ charPoly)) %ₘ charPoly := by
          rw [x_pow_period_mod]
      _ = (Polynomial.X ^ (N + k)) %ₘ charPoly := by
          rw [← Polynomial.mul_modByMonic _ _ charPoly, pow_add]
      _ = (Polynomial.X ^ (N - i) * Polynomial.X ^ j) %ₘ charPoly := by
          rw [← pow_add]; congr 2; omega
      _ = ((Polynomial.X ^ (N - i) %ₘ charPoly) * (Polynomial.X ^ j %ₘ charPoly)) %ₘ
            charPoly :=
          Polynomial.mul_modByMonic _ _ charPoly
      _ = ((Polynomial.X ^ (N - i) %ₘ charPoly) * (Polynomial.X ^ i %ₘ charPoly)) %ₘ
            charPoly := by
          rw [hEq]
      _ = (Polynomial.X ^ (N - i) * Polynomial.X ^ i) %ₘ charPoly :=
          (Polynomial.mul_modByMonic _ _ charPoly).symm
      _ = (Polynomial.X ^ N) %ₘ charPoly := by
          rw [← pow_add, Nat.sub_add_cancel (le_of_lt hi)]
      _ = 1 := x_pow_period_mod
  have hk0 := x_pow_mod_one_eq_zero hkLt hkMod
  omega

private theorem poly_surj_x_pow {f : Nat} (hfPos : 0 < f) (hfLt : f < 2 ^ 256) :
    ∃ m < 2 ^ 256 - 1, natToPoly f = (Polynomial.X ^ m) %ₘ charPoly := by
  set N := 2 ^ 256 - 1
  have hN257 : N < 2 ^ 257 := lt_trans pow256_sub_one_lt pow256_lt_pow257
  let mapPow : Fin N → Fin N := fun m =>
    let v := polyPow 2 m.val
    ⟨v - 1, by
      have hvLt := (natToPoly_polyPow 2 m.val (lt_trans m.isLt hN257) two_lt_pow256).1
      omega⟩
  have hMapNe0 : ∀ m : Fin N, polyPow 2 m.val ≠ 0 := by
    intro m hz
    have h0 := (natToPoly_polyPow 2 m.val (lt_trans m.isLt hN257) two_lt_pow256).2
    rw [hz, natToPoly_zero, natToPoly_two] at h0
    have hPer : (Polynomial.X ^ N) %ₘ charPoly = 0 := by
      have hSplit : N = (N - m.val) + m.val := by omega
      rw [hSplit, pow_add, Polynomial.mul_modByMonic _ _ charPoly, ← h0, mul_zero,
        Polynomial.zero_modByMonic]
    rw [x_pow_period_mod] at hPer
    exact one_ne_zero hPer
  have hInj : Function.Injective mapPow := by
    intro a b hab
    have hVal : polyPow 2 a.val - 1 = polyPow 2 b.val - 1 := congrArg Fin.val hab
    have haNe := hMapNe0 a
    have hbNe := hMapNe0 b
    have hEqV : polyPow 2 a.val = polyPow 2 b.val := by omega
    have hPa := (natToPoly_polyPow 2 a.val (lt_trans a.isLt hN257) two_lt_pow256).2
    have hPb := (natToPoly_polyPow 2 b.val (lt_trans b.isLt hN257) two_lt_pow256).2
    rw [hEqV] at hPa
    have hModEq := hPa.symm.trans hPb
    rw [natToPoly_two] at hModEq
    exact Fin.ext (x_pow_mod_inj a.isLt b.isLt hModEq)
  have hBij : Function.Bijective mapPow := (Fintype.bijective_iff_injective_and_card mapPow).mpr
    ⟨hInj, rfl⟩
  obtain ⟨m, hm⟩ := hBij.2 ⟨f - 1, by omega⟩
  have hV : polyPow 2 m.val = f := by
    have hVal : polyPow 2 m.val - 1 = f - 1 := congrArg Fin.val hm
    have hmNe := hMapNe0 m
    omega
  refine ⟨m.val, m.isLt, ?_⟩
  have hPm := (natToPoly_polyPow 2 m.val (lt_trans m.isLt hN257) two_lt_pow256).2
  rw [hV, natToPoly_two] at hPm
  exact hPm

def packState (r : Rng.Xoshiro256) : Nat :=
  r.s0.toNat ||| (r.s1.toNat <<< 64) ||| (r.s2.toNat <<< 128) ||| (r.s3.toNat <<< 192)

private theorem ui64_testBit_ge {w : UInt64} {i : Nat} (hi : 64 ≤ i) :
    w.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by decide) hi))

private theorem and_mask64_testBit (x k : Nat) :
    (x &&& mask64).testBit k = (decide (k < 64) && x.testBit k) := by
  simp only [mask64, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_mod_two_pow, Bool.and_comm]

private theorem and_mask64_lt (x : Nat) : x &&& mask64 < 2 ^ 64 := by
  simp only [mask64, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

private theorem packState_testBit (r : Rng.Xoshiro256) (k : Nat) :
    (packState r).testBit k =
      if k < 64 then r.s0.toNat.testBit k
      else if k < 128 then r.s1.toNat.testBit (k - 64)
      else if k < 192 then r.s2.toNat.testBit (k - 128)
      else if k < 256 then r.s3.toNat.testBit (k - 192)
      else false := by
  unfold packState
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h0 : k < 64
  · have h1 : ¬ 64 ≤ k := by omega
    have h2 : ¬ 128 ≤ k := by omega
    have h3 : ¬ 192 ≤ k := by omega
    simp [h0, h1, h2, h3]
  · by_cases h1 : k < 128
    · have hb0 := ui64_testBit_ge (w := r.s0) (by omega : 64 ≤ k)
      have h2 : ¬ 128 ≤ k := by omega
      have h3 : ¬ 192 ≤ k := by omega
      simp [h0, h1, h2, h3, hb0, show 64 ≤ k by omega]
    · by_cases h2 : k < 192
      · have hb0 := ui64_testBit_ge (w := r.s0) (by omega : 64 ≤ k)
        have hb1 := ui64_testBit_ge (w := r.s1) (by omega : 64 ≤ k - 64)
        have h3 : ¬ 192 ≤ k := by omega
        simp [h0, h1, h2, h3, hb0, hb1, show 128 ≤ k by omega]
      · by_cases h3 : k < 256
        · have hb0 := ui64_testBit_ge (w := r.s0) (by omega : 64 ≤ k)
          have hb1 := ui64_testBit_ge (w := r.s1) (by omega : 64 ≤ k - 64)
          have hb2 := ui64_testBit_ge (w := r.s2) (by omega : 64 ≤ k - 128)
          simp [h0, h1, h2, h3, hb0, hb1, hb2, show 192 ≤ k by omega]
        · have hb0 := ui64_testBit_ge (w := r.s0) (by omega : 64 ≤ k)
          have hb1 := ui64_testBit_ge (w := r.s1) (by omega : 64 ≤ k - 64)
          have hb2 := ui64_testBit_ge (w := r.s2) (by omega : 64 ≤ k - 128)
          have hb3 := ui64_testBit_ge (w := r.s3) (by omega : 64 ≤ k - 192)
          simp [h0, h1, h2, h3, hb0, hb1, hb2, hb3]

private theorem packState_lt (r : Rng.Xoshiro256) : packState r < 2 ^ 256 := by
  apply lt_two_pow_of_testBit_eq_false
  intro k hk
  rw [packState_testBit]
  simp [show ¬ k < 64 by omega, show ¬ k < 128 by omega,
    show ¬ k < 192 by omega, show ¬ k < 256 by omega]

private theorem packState_lanes (r : Rng.Xoshiro256) :
    (packState r &&& mask64 = r.s0.toNat) ∧
    ((packState r >>> 64) &&& mask64 = r.s1.toNat) ∧
    ((packState r >>> 128) &&& mask64 = r.s2.toNat) ∧
    ((packState r >>> 192) &&& mask64 = r.s3.toNat) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [and_mask64_testBit, packState_testBit]
    by_cases hi : i < 64
    · simp [hi]
    · rw [decide_eq_false hi, Bool.false_and]
      exact (ui64_testBit_ge (w := r.s0) (by omega : 64 ≤ i)).symm
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [and_mask64_testBit, Nat.testBit_shiftRight, packState_testBit]
    by_cases hi : i < 64
    · have h0 : ¬ 64 + i < 64 := by omega
      have h1 : 64 + i < 128 := by omega
      simp [hi, h0, h1]
    · rw [decide_eq_false hi, Bool.false_and]
      exact (ui64_testBit_ge (w := r.s1) (by omega : 64 ≤ i)).symm
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [and_mask64_testBit, Nat.testBit_shiftRight, packState_testBit]
    by_cases hi : i < 64
    · have h0 : ¬ 128 + i < 64 := by omega
      have h1 : ¬ 128 + i < 128 := by omega
      have h2 : 128 + i < 192 := by omega
      simp [hi, h0, h1, h2]
    · rw [decide_eq_false hi, Bool.false_and]
      exact (ui64_testBit_ge (w := r.s2) (by omega : 64 ≤ i)).symm
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [and_mask64_testBit, Nat.testBit_shiftRight, packState_testBit]
    by_cases hi : i < 64
    · have h0 : ¬ 192 + i < 64 := by omega
      have h1 : ¬ 192 + i < 128 := by omega
      have h2 : ¬ 192 + i < 192 := by omega
      have h3 : 192 + i < 256 := by omega
      simp [hi, h0, h1, h2, h3]
    · rw [decide_eq_false hi, Bool.false_and]
      exact (ui64_testBit_ge (w := r.s3) (by omega : 64 ≤ i)).symm

private theorem packState_inj {r1 r2 : Rng.Xoshiro256} (h : packState r1 = packState r2) :
    r1 = r2 := by
  have l1 := packState_lanes r1
  have l2 := packState_lanes r2
  have hs0 : r1.s0 = r2.s0 := UInt64.toNat.inj (by rw [← l1.1, h, l2.1])
  have hs1 : r1.s1 = r2.s1 := UInt64.toNat.inj (by rw [← l1.2.1, h, l2.2.1])
  have hs2 : r1.s2 = r2.s2 := UInt64.toNat.inj (by rw [← l1.2.2.1, h, l2.2.2.1])
  have hs3 : r1.s3 = r2.s3 := UInt64.toNat.inj (by rw [← l1.2.2.2, h, l2.2.2.2])
  exact congr (congr (congr (congrArg Rng.Xoshiro256.mk hs0) hs1) hs2) hs3

private theorem ui64_shl17_toNat (a : UInt64) :
    (a <<< 17).toNat = (a.toNat <<< 17) &&& mask64 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [UInt64.toNat_shiftLeft, show (17 : UInt64).toNat % 64 = 17 by decide,
    and_mask64_testBit, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]

private theorem ui64_rotl45_toNat (a : UInt64) :
    (Rng.rotateLeft a 45).toNat = ((a.toNat <<< 45) &&& mask64) ||| (a.toNat >>> 19) := by
  unfold Rng.rotateLeft
  have h1 : ((45 : UInt64) &&& 63).toNat % 64 = 45 := by decide
  have h2 : ((64 - (45 : UInt64)) &&& 63).toNat % 64 = 19 := by decide
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, h1, h2]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, and_mask64_testBit, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]

private theorem packState_next (r : Rng.Xoshiro256) :
    packState r.next.2 = stepNat (packState r) := by
  have hl := packState_lanes r
  unfold Rng.Xoshiro256.next stepNat
  dsimp only
  rw [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2]
  dsimp only [packState]
  simp only [UInt64.toNat_xor, ui64_shl17_toNat, ui64_rotl45_toNat]

private theorem packState_advance (k : Nat) (r : Rng.Xoshiro256) :
    packState (Rng.advance k r) = iterStep k (packState r) := by
  induction k generalizing r with
  | zero => rfl
  | succ m ih =>
    change packState (Rng.advance m r.next.2) = iterStep m (stepNat (packState r))
    rw [ih r.next.2, packState_next]

private theorem stepNat_zero : stepNat 0 = 0 := by decide

private theorem pack4_lt {a0 a1 a2 a3 : Nat}
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) :
    (a0 ||| (a1 <<< 64) ||| (a2 <<< 128) ||| (a3 <<< 192)) < 2 ^ 256 := by
  apply lt_two_pow_of_testBit_eq_false
  intro k hk
  have hge : ∀ {x : Nat} (i : Nat), x < 2 ^ 64 → 64 ≤ i → x.testBit i = false :=
    fun {_} i hx hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  simp [show 64 ≤ k by omega, show 128 ≤ k by omega, show 192 ≤ k by omega,
    hge k ha0 (by omega), hge (k - 64) ha1 (by omega), hge (k - 128) ha2 (by omega),
    hge (k - 192) ha3 (by omega)]

private theorem xor_land (a b m : Nat) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [Nat.testBit_xor, Nat.testBit_and, Bool.and_xor_distrib_right]

private theorem xor_shiftLeft (a b s : Nat) : (a ^^^ b) <<< s = (a <<< s) ^^^ (b <<< s) := by
  apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases h : s ≤ k <;> simp [h]

private theorem xor_shiftRight (a b s : Nat) : (a ^^^ b) >>> s = (a >>> s) ^^^ (b >>> s) := by
  apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_xor, Nat.testBit_shiftRight]

private theorem rotl45_xor (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (((x ^^^ y) <<< 45) &&& mask64) ||| ((x ^^^ y) >>> 19) =
      ((((x <<< 45) &&& mask64) ||| (x >>> 19)) ^^^ (((y <<< 45) &&& mask64) ||| (y >>> 19))) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, and_mask64_testBit, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases hi : i < 64
  · by_cases hi45 : i < 45
    · have h45 : ¬ 45 ≤ i := by omega
      simp [hi, h45]
    · have hi19 : 64 ≤ 19 + i := by omega
      have hX0 := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi19))
      have hY0 := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi19))
      simp [hi, show 45 ≤ i by omega, hX0, hY0]
  · have h64 : 64 ≤ 19 + i := by omega
    have hX0 := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h64))
    have hY0 := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) h64))
    simp [hi, hX0, hY0]

private theorem rotl45_lt {x : Nat} (hx : x < 2 ^ 64) :
    (((x <<< 45) &&& mask64) ||| (x >>> 19)) < 2 ^ 64 := by
  apply lt_two_pow_of_testBit_eq_false
  intro k hk
  simp only [Nat.testBit_or, and_mask64_testBit, Nat.testBit_shiftRight]
  have hK : decide (k < 64) = false := decide_eq_false (by omega)
  have hx0 := Nat.testBit_lt_two_pow
    (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ 19 + k)))
  simp [hK, hx0]

private theorem stepNat_lt {v : Nat} : stepNat v < 2 ^ 256 := by
  have hLt := and_mask64_lt
  have h3a : ((v >>> 192 &&& mask64) ^^^ (v >>> 64 &&& mask64)) < 2 ^ 64 :=
    Nat.xor_lt_two_pow (hLt _) (hLt _)
  have h2a : ((v >>> 128 &&& mask64) ^^^ (v &&& mask64)) < 2 ^ 64 :=
    Nat.xor_lt_two_pow (hLt _) (hLt _)
  exact pack4_lt
    (Nat.xor_lt_two_pow (hLt _) h3a)
    (Nat.xor_lt_two_pow (hLt _) h2a)
    (Nat.xor_lt_two_pow h2a (hLt _))
    (rotl45_lt h3a)

private theorem pack4_xor {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (_ha3 : a3 < 2 ^ 64)
    (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (_hb3 : b3 < 2 ^ 64) :
    ((a0 ^^^ b0) ||| ((a1 ^^^ b1) <<< 64) ||| ((a2 ^^^ b2) <<< 128) ||| ((a3 ^^^ b3) <<< 192)) =
      (a0 ||| (a1 <<< 64) ||| (a2 <<< 128) ||| (a3 <<< 192)) ^^^
        (b0 ||| (b1 <<< 64) ||| (b2 <<< 128) ||| (b3 <<< 192)) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_xor]
  have hge : ∀ {x : Nat} (i : Nat), x < 2 ^ 64 → 64 ≤ i → x.testBit i = false :=
    fun {_} i hx hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
  by_cases h64 : k < 64
  · simp [show ¬ 64 ≤ k by omega, show ¬ 128 ≤ k by omega, show ¬ 192 ≤ k by omega]
  · by_cases h128 : k < 128
    · simp [show 64 ≤ k by omega, show ¬ 128 ≤ k by omega, show ¬ 192 ≤ k by omega,
        hge k ha0 (by omega), hge k hb0 (by omega)]
    · by_cases h192 : k < 192
      · simp [show 64 ≤ k by omega, show 128 ≤ k by omega, show ¬ 192 ≤ k by omega,
          hge k ha0 (by omega), hge k hb0 (by omega),
          hge (k - 64) ha1 (by omega), hge (k - 64) hb1 (by omega)]
      · simp [show 64 ≤ k by omega, show 128 ≤ k by omega, show 192 ≤ k by omega,
          hge k ha0 (by omega), hge k hb0 (by omega),
          hge (k - 64) ha1 (by omega), hge (k - 64) hb1 (by omega),
          hge (k - 128) ha2 (by omega), hge (k - 128) hb2 (by omega)]

private theorem xor4_reassoc (a b c d : Nat) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> cases c.testBit k <;> cases d.testBit k <;> rfl

private theorem stepNat_xor (u v : Nat) : stepNat (u ^^^ v) = stepNat u ^^^ stepNat v := by
  unfold stepNat
  dsimp only
  rw [xor_shiftRight u v 64, xor_shiftRight u v 128, xor_shiftRight u v 192]
  simp only [xor_land]
  have hLt : ∀ x, x &&& mask64 < 2 ^ 64 := and_mask64_lt
  set u0 := u &&& mask64
  set u1 := (u >>> 64) &&& mask64
  set u2 := (u >>> 128) &&& mask64
  set u3 := (u >>> 192) &&& mask64
  set v0 := v &&& mask64
  set v1 := (v >>> 64) &&& mask64
  set v2 := (v >>> 128) &&& mask64
  set v3 := (v >>> 192) &&& mask64
  have hu0Lt := hLt u
  have hu1Lt := hLt (u >>> 64)
  have hu2Lt := hLt (u >>> 128)
  have hu3Lt := hLt (u >>> 192)
  have hv0Lt := hLt v
  have hv1Lt := hLt (v >>> 64)
  have hv2Lt := hLt (v >>> 128)
  have hv3Lt := hLt (v >>> 192)
  have hs2a : (u2 ^^^ v2) ^^^ (u0 ^^^ v0) = (u2 ^^^ u0) ^^^ (v2 ^^^ v0) := xor4_reassoc _ _ _ _
  have hs3a : (u3 ^^^ v3) ^^^ (u1 ^^^ v1) = (u3 ^^^ u1) ^^^ (v3 ^^^ v1) := xor4_reassoc _ _ _ _
  have hs1b : (u1 ^^^ v1) ^^^ ((u2 ^^^ u0) ^^^ (v2 ^^^ v0)) =
      (u1 ^^^ (u2 ^^^ u0)) ^^^ (v1 ^^^ (v2 ^^^ v0)) := xor4_reassoc _ _ _ _
  have hs0b : (u0 ^^^ v0) ^^^ ((u3 ^^^ u1) ^^^ (v3 ^^^ v1)) =
      (u0 ^^^ (u3 ^^^ u1)) ^^^ (v0 ^^^ (v3 ^^^ v1)) := xor4_reassoc _ _ _ _
  have hs2b : ((u2 ^^^ u0) ^^^ (v2 ^^^ v0)) ^^^
      (((u1 <<< 17) &&& mask64) ^^^ ((v1 <<< 17) &&& mask64)) =
      ((u2 ^^^ u0) ^^^ ((u1 <<< 17) &&& mask64)) ^^^
      ((v2 ^^^ v0) ^^^ ((v1 <<< 17) &&& mask64)) := xor4_reassoc _ _ _ _
  have hu3aLt : (u3 ^^^ u1) < 2 ^ 64 := Nat.xor_lt_two_pow hu3Lt hu1Lt
  have hv3aLt : (v3 ^^^ v1) < 2 ^ 64 := Nat.xor_lt_two_pow hv3Lt hv1Lt
  have hRot := rotl45_xor (u3 ^^^ u1) (v3 ^^^ v1) hu3aLt hv3aLt
  rw [xor_shiftLeft u1 v1 17, xor_land, hs2a, hs3a, hs1b, hs0b, hs2b, hRot]
  exact pack4_xor
    (Nat.xor_lt_two_pow hu0Lt hu3aLt)
    (Nat.xor_lt_two_pow hu1Lt (Nat.xor_lt_two_pow hu2Lt hu0Lt))
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hu2Lt hu0Lt) (hLt (u1 <<< 17)))
    (rotl45_lt hu3aLt)
    (Nat.xor_lt_two_pow hv0Lt hv3aLt)
    (Nat.xor_lt_two_pow hv1Lt (Nat.xor_lt_two_pow hv2Lt hv0Lt))
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hv2Lt hv0Lt) (hLt (v1 <<< 17)))
    (rotl45_lt hv3aLt)

private theorem evalPolyGo_acc :
    ∀ n f cur acc : Nat, evalPolyGo n f cur acc = acc ^^^ evalPolyGo n f cur 0
  | 0, _, _, acc => by simp [evalPolyGo]
  | n + 1, f, cur, acc => by
    unfold evalPolyGo
    dsimp only
    by_cases hOdd : (f &&& 1 == 1) = true
    · simp only [hOdd, ↓reduceIte, Nat.zero_xor]
      rw [evalPolyGo_acc n (f >>> 1) (stepNat cur) (acc ^^^ cur),
        evalPolyGo_acc n (f >>> 1) (stepNat cur) cur, Nat.xor_assoc]
    · have hEven : (f &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
      simp only [hEven, Bool.false_eq_true, ↓reduceIte]
      exact evalPolyGo_acc n (f >>> 1) (stepNat cur) acc

private theorem evalPolyGo_xor :
    ∀ n f g cur : Nat,
      evalPolyGo n (f ^^^ g) cur 0 = evalPolyGo n f cur 0 ^^^ evalPolyGo n g cur 0
  | 0, _, _, _ => by simp [evalPolyGo]
  | n + 1, f, g, cur => by
    unfold evalPolyGo
    dsimp only
    rw [xor_land, xor_shiftRight]
    have hfMod : (f &&& 1 = 0) ∨ (f &&& 1 = 1) := by
      have hm := Nat.mod_lt f (by decide : 0 < 2)
      rw [Nat.and_one_is_mod]
      omega
    have hgMod : (g &&& 1 = 0) ∨ (g &&& 1 = 1) := by
      have hm := Nat.mod_lt g (by decide : 0 < 2)
      rw [Nat.and_one_is_mod]
      omega
    rcases hfMod with hfB | hfB <;> rcases hgMod with hgB | hgB
    · simp only [hfB, hgB, Nat.xor_zero,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      exact evalPolyGo_xor n (f >>> 1) (g >>> 1) (stepNat cur)
    · simp only [hfB, hgB, Nat.zero_xor, beq_self_eq_true,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [evalPolyGo_acc n (g >>> 1) (stepNat cur) cur,
        evalPolyGo_acc n ((f >>> 1) ^^^ (g >>> 1)) (stepNat cur) cur,
        evalPolyGo_xor n (f >>> 1) (g >>> 1) (stepNat cur)]
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_xor]
      cases cur.testBit k <;>
        cases (evalPolyGo n (f >>> 1) (stepNat cur) 0).testBit k <;>
        cases (evalPolyGo n (g >>> 1) (stepNat cur) 0).testBit k <;> rfl
    · simp only [hfB, hgB, Nat.xor_zero, Nat.zero_xor, beq_self_eq_true,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [evalPolyGo_acc n (f >>> 1) (stepNat cur) cur,
        evalPolyGo_acc n ((f >>> 1) ^^^ (g >>> 1)) (stepNat cur) cur,
        evalPolyGo_xor n (f >>> 1) (g >>> 1) (stepNat cur), Nat.xor_assoc]
    · simp only [hfB, hgB, Nat.xor_self, show (0 == 1) = false by decide,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      rw [evalPolyGo_acc n (f >>> 1) (stepNat cur) cur,
        evalPolyGo_acc n (g >>> 1) (stepNat cur) cur,
        evalPolyGo_xor n (f >>> 1) (g >>> 1) (stepNat cur)]
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_xor]
      cases cur.testBit k <;>
        cases (evalPolyGo n (f >>> 1) (stepNat cur) 0).testBit k <;>
        cases (evalPolyGo n (g >>> 1) (stepNat cur) 0).testBit k <;> rfl

private theorem evalPoly_xor (f g : Nat) : evalPoly (f ^^^ g) = evalPoly f ^^^ evalPoly g :=
  evalPolyGo_xor 256 f g 1

private theorem evalPolyGo_zero : ∀ n cur : Nat, evalPolyGo n 0 cur 0 = 0
  | 0, _ => rfl
  | n + 1, cur => by
    unfold evalPolyGo
    simp [evalPolyGo_zero n (stepNat cur)]

private theorem evalPoly_zero : evalPoly 0 = 0 := evalPolyGo_zero 256 1

private theorem evalPolyGo_lt :
    ∀ n f cur acc : Nat, cur < 2 ^ 256 → acc < 2 ^ 256 → evalPolyGo n f cur acc < 2 ^ 256
  | 0, _, _, acc, _, hacc => hacc
  | n + 1, f, cur, acc, hcur, hacc => by
    unfold evalPolyGo
    dsimp only
    split
    · exact evalPolyGo_lt n (f >>> 1) (stepNat cur) (acc ^^^ cur) stepNat_lt
        (Nat.xor_lt_two_pow hacc hcur)
    · exact evalPolyGo_lt n (f >>> 1) (stepNat cur) acc stepNat_lt hacc

private theorem evalPoly_lt (f : Nat) : evalPoly f < 2 ^ 256 :=
  evalPolyGo_lt 256 f 1 0 one_lt_pow256 pow256_pos

private theorem evalBinvGo_lt :
    ∀ (bs : List Nat) (v acc : Nat),
      bs.all (fun b => decide (b < 2 ^ 256)) = true → acc < 2 ^ 256 →
      evalBinvGo v bs acc < 2 ^ 256
  | [], _, acc, _, hacc => hacc
  | b :: rest, v, acc, hAll, hacc => by
    have hPair := Bool.and_eq_true_iff.mp hAll
    have hbLt : b < 2 ^ 256 := of_decide_eq_true hPair.1
    unfold evalBinvGo
    split
    · exact evalBinvGo_lt rest (v >>> 1) (acc ^^^ b) hPair.2 (Nat.xor_lt_two_pow hacc hbLt)
    · exact evalBinvGo_lt rest (v >>> 1) acc hPair.2 hacc

private theorem evalBinv_lt (v : Nat) : evalBinv v < 2 ^ 256 :=
  evalBinvGo_lt invBasisList v 0 invBasisList_lt pow256_pos

private theorem one_shiftLeft_xor_even_shift {q idx : Nat} :
    (1 <<< idx) ^^^ ((q <<< 1) <<< idx) = ((2 * q + 1) <<< idx) := by
  rw [← xor_shiftLeft]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  cases k with
  | zero =>
    have h0 : (q <<< 1).testBit 0 = false := by simp
    have h1 : (1 : Nat).testBit 0 = true := by decide
    have hR : (2 * q + 1).testBit 0 = true := by simp [Nat.testBit_zero]
    rw [h0, h1, hR]; rfl
  | succ m =>
    have h1 : (1 : Nat).testBit (m + 1) = false :=
      Bool.eq_false_iff.mpr fun h => by
        have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h; omega
    have hQ : (q <<< 1).testBit (m + 1) = q.testBit m := by
      simp [Nat.testBit_shiftLeft]
    have hR : (2 * q + 1).testBit (m + 1) = q.testBit m := by
      rw [Nat.testBit_succ, show (2 * q + 1) / 2 = q by omega]
    rw [h1, hQ, hR, Bool.false_xor]

private theorem evalPoly_evalBinvGo :
    ∀ (bs : List Nat) (idx v acc : Nat),
      v < 2 ^ bs.length → checkInvBasisB idx bs = true →
      evalPoly (evalBinvGo v bs acc) = evalPoly acc ^^^ (v <<< idx)
  | [], idx, v, acc, hv, _ => by
    have hv0 : v = 0 := by rw [List.length_nil, Nat.pow_zero] at hv; omega
    subst hv0
    simp [evalBinvGo]
  | b :: rest, idx, v, acc, hv, hChk => by
    rw [checkInvBasisB] at hChk
    have hPair := Bool.and_eq_true_iff.mp hChk
    have hbEq : evalPoly b = 1 <<< idx := eq_of_beq hPair.1
    have hvHalf : v >>> 1 < 2 ^ rest.length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm] at hv
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact Nat.div_lt_of_lt_mul hv
    unfold evalBinvGo
    have hMod : v &&& 1 = v % 2 := Nat.and_one_is_mod v
    by_cases hOdd : (v &&& 1 == 1) = true
    · simp only [hOdd, ↓reduceIte]
      have ih := evalPoly_evalBinvGo rest (idx + 1) (v >>> 1) (acc ^^^ b) hvHalf hPair.2
      rw [ih, evalPoly_xor, hbEq]
      have hVMod : v % 2 = 1 := by have := eq_of_beq hOdd; omega
      have hvDecomp : v = 2 * (v >>> 1) + 1 := by rw [Nat.shiftRight_eq_div_pow]; omega
      have hShift : (v >>> 1) <<< (idx + 1) = (((v >>> 1) <<< 1) <<< idx) := by
        simp only [Nat.shiftLeft_eq, Nat.pow_succ]
        ring
      rw [hShift, Nat.xor_assoc, one_shiftLeft_xor_even_shift]
      conv_rhs => rw [hvDecomp]
    · have hEven : (v &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
      simp only [hEven, Bool.false_eq_true, ↓reduceIte]
      have ih := evalPoly_evalBinvGo rest (idx + 1) (v >>> 1) acc hvHalf hPair.2
      rw [ih]
      have hVMod : v % 2 ≠ 1 := fun h => hOdd (by rw [hMod, h]; rfl)
      have hvDecomp : v = 2 * (v >>> 1) := by rw [Nat.shiftRight_eq_div_pow]; omega
      have hShift : (v >>> 1) <<< (idx + 1) = (2 * (v >>> 1)) <<< idx := by
        simp only [Nat.shiftLeft_eq, Nat.pow_succ]
        ring
      rw [hShift, ← hvDecomp]

private theorem evalPoly_evalBinv {v : Nat} (hv : v < 2 ^ 256) :
    evalPoly (evalBinv v) = v := by
  have hvLen : v < 2 ^ invBasisList.length := by rw [invBasisList_len]; exact hv
  have h := evalPoly_evalBinvGo invBasisList 0 v 0 hvLen b_invbasis_check
  simpa [evalBinv, evalPoly_zero] using h

private theorem evalBinvGo_acc :
    ∀ (bs : List Nat) (v acc : Nat), evalBinvGo v bs acc = acc ^^^ evalBinvGo v bs 0
  | [], _, acc => by simp [evalBinvGo]
  | b :: rest, v, acc => by
    unfold evalBinvGo
    dsimp only
    by_cases hOdd : (v &&& 1 == 1) = true
    · simp only [hOdd, ↓reduceIte, Nat.zero_xor]
      rw [evalBinvGo_acc rest (v >>> 1) (acc ^^^ b),
        evalBinvGo_acc rest (v >>> 1) b, Nat.xor_assoc]
    · have hEven : (v &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
      simp only [hEven, Bool.false_eq_true, ↓reduceIte]
      exact evalBinvGo_acc rest (v >>> 1) acc

private theorem evalBinvGo_xor :
    ∀ (bs : List Nat) (u v : Nat),
      evalBinvGo (u ^^^ v) bs 0 = evalBinvGo u bs 0 ^^^ evalBinvGo v bs 0
  | [], _, _ => by simp [evalBinvGo]
  | b :: rest, u, v => by
    unfold evalBinvGo
    dsimp only
    rw [xor_land, xor_shiftRight]
    have huMod : (u &&& 1 = 0) ∨ (u &&& 1 = 1) := by rw [Nat.and_one_is_mod]; omega
    have hvMod : (v &&& 1 = 0) ∨ (v &&& 1 = 1) := by rw [Nat.and_one_is_mod]; omega
    rcases huMod with huB | huB <;> rcases hvMod with hvB | hvB
    · simp only [huB, hvB, Nat.xor_zero,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      exact evalBinvGo_xor rest (u >>> 1) (v >>> 1)
    · simp only [huB, hvB, Nat.zero_xor, beq_self_eq_true,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [evalBinvGo_acc rest (v >>> 1) b,
        evalBinvGo_acc rest ((u >>> 1) ^^^ (v >>> 1)) b,
        evalBinvGo_xor rest (u >>> 1) (v >>> 1)]
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_xor]
      cases b.testBit k <;>
        cases (evalBinvGo (u >>> 1) rest 0).testBit k <;>
        cases (evalBinvGo (v >>> 1) rest 0).testBit k <;> rfl
    · simp only [huB, hvB, Nat.xor_zero, Nat.zero_xor, beq_self_eq_true,
        show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [evalBinvGo_acc rest (u >>> 1) b,
        evalBinvGo_acc rest ((u >>> 1) ^^^ (v >>> 1)) b,
        evalBinvGo_xor rest (u >>> 1) (v >>> 1), Nat.xor_assoc]
    · simp only [huB, hvB, Nat.xor_self, show (0 == 1) = false by decide,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      rw [evalBinvGo_acc rest (u >>> 1) b, evalBinvGo_acc rest (v >>> 1) b,
        evalBinvGo_xor rest (u >>> 1) (v >>> 1)]
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_xor]
      cases b.testBit k <;>
        cases (evalBinvGo (u >>> 1) rest 0).testBit k <;>
        cases (evalBinvGo (v >>> 1) rest 0).testBit k <;> rfl

private theorem evalBinv_xor (u v : Nat) : evalBinv (u ^^^ v) = evalBinv u ^^^ evalBinv v :=
  evalBinvGo_xor invBasisList u v

private theorem evalBinvGo_zero : ∀ bs : List Nat, evalBinvGo 0 bs 0 = 0
  | [] => rfl
  | _ :: rest => by unfold evalBinvGo; simp [evalBinvGo_zero rest]

private theorem evalBinv_zero : evalBinv 0 = 0 := evalBinvGo_zero invBasisList

private theorem evalBinv_evalPolyGo :
    ∀ (n k f cur : Nat),
      f < 2 ^ n → checkInvBasisLeftAt k n cur = true →
      evalBinv (evalPolyGo n f cur 0) = f <<< k
  | 0, _, f, _, hf, _ => by
    have hf0 : f = 0 := by rw [Nat.pow_zero] at hf; omega
    subst hf0
    simp [evalPolyGo, evalBinv_zero]
  | n + 1, k, f, cur, hf, hChk => by
    rw [checkInvBasisLeftAt] at hChk
    have hPair := Bool.and_eq_true_iff.mp hChk
    have hCurEq : evalBinv cur = 1 <<< k := eq_of_beq hPair.1
    have hfHalf : f >>> 1 < 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hf
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact Nat.div_lt_of_lt_mul hf
    unfold evalPolyGo
    dsimp only
    have hMod : f &&& 1 = f % 2 := Nat.and_one_is_mod f
    by_cases hOdd : (f &&& 1 == 1) = true
    · simp only [hOdd, ↓reduceIte, Nat.zero_xor]
      rw [evalPolyGo_acc, evalBinv_xor, hCurEq,
        evalBinv_evalPolyGo n (k + 1) (f >>> 1) (stepNat cur) hfHalf hPair.2]
      have hFMod : f % 2 = 1 := by have := eq_of_beq hOdd; omega
      have hfDecomp : f = 2 * (f >>> 1) + 1 := by rw [Nat.shiftRight_eq_div_pow]; omega
      have hShift : (f >>> 1) <<< (k + 1) = (((f >>> 1) <<< 1) <<< k) := by
        simp only [Nat.shiftLeft_eq, Nat.pow_succ]
        ring
      rw [hShift, one_shiftLeft_xor_even_shift]
      conv_rhs => rw [hfDecomp]
    · have hEven : (f &&& 1 == 1) = false := Bool.eq_false_iff.mpr hOdd
      simp only [hEven, Bool.false_eq_true, ↓reduceIte]
      rw [evalBinv_evalPolyGo n (k + 1) (f >>> 1) (stepNat cur) hfHalf hPair.2]
      have hFMod : f % 2 ≠ 1 := fun h => hOdd (by rw [hMod, h]; rfl)
      have hfDecomp : f = 2 * (f >>> 1) := by rw [Nat.shiftRight_eq_div_pow]; omega
      have hShift : (f >>> 1) <<< (k + 1) = (2 * (f >>> 1)) <<< k := by
        simp only [Nat.shiftLeft_eq, Nat.pow_succ]
        ring
      rw [hShift, ← hfDecomp]

private theorem evalBinv_evalPoly {f : Nat} (hf : f < 2 ^ 256) :
    evalBinv (evalPoly f) = f := by
  have h := evalBinv_evalPolyGo 256 0 f 1 hf b_invbasis_left_check
  simpa [evalPoly] using h

private theorem evalPoly_inj {f g : Nat} (hf : f < 2 ^ 256) (hg : g < 2 ^ 256)
    (h : evalPoly f = evalPoly g) : f = g := by
  rw [← evalBinv_evalPoly hf, ← evalBinv_evalPoly hg, h]

private theorem evalPolyGo_stepNat :
    ∀ n f c acc : Nat,
      stepNat (evalPolyGo n f c acc) = evalPolyGo n f (stepNat c) (stepNat acc)
  | 0, _, _, _ => rfl
  | n + 1, f, c, acc => by
    unfold evalPolyGo
    dsimp only
    split
    · rw [evalPolyGo_stepNat n (f >>> 1) (stepNat c) (acc ^^^ c), stepNat_xor]
    · exact evalPolyGo_stepNat n (f >>> 1) (stepNat c) acc

private theorem evalPolyGo_succ_of_lt :
    ∀ n f c acc : Nat, f < 2 ^ n →
      evalPolyGo (n + 1) f c acc = evalPolyGo n f c acc
  | 0, f, c, acc, hf => by
    have hf0 : f = 0 := by rw [Nat.pow_zero] at hf; omega
    subst hf0
    simp [evalPolyGo]
  | n + 1, f, c, acc, hf => by
    have hfHalf : f >>> 1 < 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm] at hf
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact Nat.div_lt_of_lt_mul hf
    unfold evalPolyGo
    dsimp only
    split
    · exact evalPolyGo_succ_of_lt n (f >>> 1) (stepNat c) (acc ^^^ c) hfHalf
    · exact evalPolyGo_succ_of_lt n (f >>> 1) (stepNat c) acc hfHalf

private theorem evalPoly_shl1_lt {g : Nat} (hg : g < 2 ^ 255) :
    evalPoly (g <<< 1) = stepNat (evalPoly g) := by
  unfold evalPoly
  have h1 : evalPolyGo 256 (g <<< 1) 1 0 = evalPolyGo 255 g (stepNat 1) 0 := by
    have hMod : (g <<< 1) &&& 1 = 0 := by
      rw [Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_mod_left]
    have hDiv : (g <<< 1) >>> 1 = g := by
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_one]; simp
    conv_lhs =>
      unfold evalPolyGo
      simp only [hMod, hDiv, show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
  have h2 : evalPolyGo 255 g (stepNat 1) 0 = evalPolyGo 256 g (stepNat 1) (stepNat 0) := by
    rw [stepNat_zero, evalPolyGo_succ_of_lt 255 g (stepNat 1) 0 hg]
  rw [h1, h2, ← evalPolyGo_stepNat]

private theorem iterStep_succ_right :
    ∀ k v : Nat, iterStep (k + 1) v = stepNat (iterStep k v)
  | 0, _ => rfl
  | k + 1, v => iterStep_succ_right k (stepNat v)

private theorem evalPolyGo_one_shl :
    ∀ (k n c : Nat), k < n → evalPolyGo n (1 <<< k) c 0 = iterStep k c
  | 0, n + 1, c, _ => by
    have hMod : (1 <<< 0) &&& 1 = 1 := by decide
    have hDiv : (1 <<< 0) >>> 1 = 0 := by decide
    unfold evalPolyGo
    simp only [hMod, hDiv, beq_self_eq_true, ↓reduceIte, Nat.zero_xor]
    rw [evalPolyGo_acc, evalPolyGo_zero, Nat.xor_zero]
    rfl
  | k + 1, n + 1, c, hk => by
    have hMod : (1 <<< (k + 1)) &&& 1 = 0 := by
      rw [Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ, Nat.mul_mod_left]
    have hDiv : (1 <<< (k + 1)) >>> 1 = 1 <<< k := by
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.pow_one]
      simp [Nat.shiftLeft_eq]
    unfold evalPolyGo
    simp only [hMod, hDiv, show (0 == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
    exact evalPolyGo_one_shl k n (stepNat c) (by omega)

private theorem stepNat_bit255 : stepNat (evalPoly (1 <<< 255)) = evalPoly pLow := by
  unfold evalPoly
  rw [evalPolyGo_one_shl 255 256 1 (by decide), ← iterStep_succ_right, ← charpoly_check]
  rfl

private theorem evalPoly_polyMul_two {f : Nat} (hf : f < 2 ^ 256) :
    evalPoly (polyMul f 2) = stepNat (evalPoly f) := by
  have hm := natToPoly_polyMul hf two_lt_pow256
  have hMulX :
      (natToPoly f * natToPoly 2) %ₘ charPoly = (natToPoly f * Polynomial.X) %ₘ charPoly := by
    rw [natToPoly_two]
  have hPow256 : (2 ^ 256 : Nat) = 2 * 2 ^ 255 := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases h255 : f < 2 ^ 255
  · have hDeg : (natToPoly f * Polynomial.X).degree < charPoly.degree := by
      rw [charPoly_degree]
      have hD1 : (natToPoly f).degree < (255 : WithBot ℕ) := natToPoly_degree_lt f 255 h255
      calc (natToPoly f * Polynomial.X).degree
          ≤ (natToPoly f).degree + (Polynomial.X : Polynomial (ZMod 2)).degree :=
            Polynomial.degree_mul_le _ _
        _ < (255 : WithBot ℕ) + (1 : WithBot ℕ) := by
            rw [Polynomial.degree_X]
            exact WithBot.add_lt_add_right WithBot.coe_ne_bot hD1
        _ = (256 : WithBot ℕ) := rfl
    have hShlPoly : natToPoly (f <<< 1) = natToPoly f * Polynomial.X := by
      simpa [Nat.shiftLeft_eq] using natToPoly_shiftLeft f 1
    have hModSelf : (natToPoly f * Polynomial.X) %ₘ charPoly = natToPoly (f <<< 1) := by
      rw [← hShlPoly]
      exact (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr (by rw [hShlPoly]; exact hDeg)
    have hPM : polyMul f 2 = f <<< 1 := natToPoly_inj (hm.2.trans (hMulX.trans hModSelf))
    rw [hPM]
    exact evalPoly_shl1_lt h255
  · have hfGe : 2 ^ 255 ≤ f := Nat.le_of_not_lt h255
    set fLo := f &&& mask255
    have hfLoLt : fLo < 2 ^ 255 := and_mask255_lt f
    have hfDiv : f / 2 ^ 255 = 1 :=
      Nat.div_eq_of_lt_le (Nat.one_mul (2 ^ 255) ▸ hfGe) (by rw [hPow256] at hf; exact hf)
    have hfDecomp : f = fLo ^^^ (1 <<< 255) := by
      apply Nat.eq_of_testBit_eq; intro k
      simp only [fLo, mask255_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
      by_cases hk : k < 255
      · have hne : 255 ≠ k := by omega
        simp [hk, hne]
      · by_cases hk255 : k = 255
        · subst hk255
          have hb : f.testBit 255 = true := by
            rw [Nat.testBit_eq_decide_div_mod_eq, hfDiv]
            decide
          simp [hb]
        · have hfZero := Nat.testBit_lt_two_pow
            (lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) (by omega : 256 ≤ k)))
          simp [hk, show 255 ≠ k by omega, hfZero]
    set res := (fLo <<< 1) ^^^ pLow
    have hfLo2Lt : fLo <<< 1 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm, hPow256]
      exact Nat.mul_lt_mul_of_pos_left hfLoLt (by decide)
    have hResLt : res < 2 ^ 256 := Nat.xor_lt_two_pow hfLo2Lt pLow_lt
    have hResPoly : natToPoly res = natToPoly fLo * Polynomial.X + natToPoly pLow := by
      have hShl : natToPoly (fLo <<< 1) = natToPoly fLo * Polynomial.X := by
        simpa [Nat.shiftLeft_eq] using natToPoly_shiftLeft fLo 1
      rw [natToPoly_xor, hShl]
    have hFXEq : natToPoly f * Polynomial.X = natToPoly res + charPoly := by
      have hF : natToPoly f = natToPoly fLo + Polynomial.X ^ 255 := by
        rw [hfDecomp, natToPoly_xor, natToPoly_shiftLeft, natToPoly_one, one_mul]
      have hZ := poly_add_self_zmod2 (natToPoly pLow)
      rw [hF, hResPoly, charPoly]
      calc (natToPoly fLo + Polynomial.X ^ 255) * Polynomial.X
          = natToPoly fLo * Polynomial.X + Polynomial.X ^ 256 + 0 := by ring
        _ = natToPoly fLo * Polynomial.X + Polynomial.X ^ 256 +
              (natToPoly pLow + natToPoly pLow) := by rw [hZ]
        _ = (natToPoly fLo * Polynomial.X + natToPoly pLow) +
              (Polynomial.X ^ 256 + natToPoly pLow) := by ring
    have hModEq : (natToPoly f * Polynomial.X) %ₘ charPoly = natToPoly res := by
      rw [hFXEq, add_charPoly_modByMonic, Polynomial.modByMonic_eq_self_iff charPoly_monic,
        charPoly_degree]
      exact natToPoly_degree_lt res 256 hResLt
    have hPM : polyMul f 2 = res := natToPoly_inj (hm.2.trans (hMulX.trans hModEq))
    rw [hPM]
    dsimp only [res]
    rw [evalPoly_xor, evalPoly_shl1_lt hfLoLt, ← stepNat_bit255, ← stepNat_xor,
      ← evalPoly_xor, ← hfDecomp]

private theorem iterStep_add :
    ∀ m n v : Nat, iterStep (m + n) v = iterStep m (iterStep n v)
  | 0, _, _ => by simp [iterStep]
  | m + 1, n, v => by
    rw [Nat.add_right_comm, iterStep_succ_right, iterStep_succ_right, iterStep_add m n v]

private theorem iterStep_evalPoly :
    ∀ k f : Nat, k < 2 ^ 256 → f < 2 ^ 256 →
      iterStep k (evalPoly f) = evalPoly (polyMul f (polyPow 2 k))
  | 0, f, _, hf => by
    have hPow0 : polyPow 2 0 = 1 := by decide
    have hm := natToPoly_polyMul hf one_lt_pow256
    have hMod1 : (natToPoly f * natToPoly 1) %ₘ charPoly = natToPoly f := by
      rw [natToPoly_one, mul_one, Polynomial.modByMonic_eq_self_iff charPoly_monic,
        charPoly_degree]
      exact natToPoly_degree_lt f 256 hf
    have hEq : polyMul f 1 = f := natToPoly_inj (hm.2.trans hMod1)
    rw [hPow0, hEq, iterStep]
  | k + 1, f, hk, hf => by
    have hkLt : k < 2 ^ 256 := Nat.lt_of_succ_lt hk
    have hk1Lt257 : k + 1 < 2 ^ 257 := lt_trans hk pow256_lt_pow257
    have hkLt257 : k < 2 ^ 257 := lt_trans hkLt pow256_lt_pow257
    have ih := iterStep_evalPoly k f hkLt hf
    rw [iterStep_succ_right, ih, ← evalPoly_polyMul_two (natToPoly_polyMul hf
      (natToPoly_polyPow 2 k hkLt257 two_lt_pow256).1).1]
    apply congrArg evalPoly
    apply natToPoly_inj
    have hPk := natToPoly_polyPow 2 k hkLt257 two_lt_pow256
    have hPk1 := natToPoly_polyPow 2 (k + 1) hk1Lt257 two_lt_pow256
    have hM1 := natToPoly_polyMul hf hPk.1
    have hM2 := natToPoly_polyMul hM1.1 two_lt_pow256
    have hM3 := natToPoly_polyMul hf hPk1.1
    rw [hM2.2, hM1.2, hM3.2, hPk.2, hPk1.2, natToPoly_two]
    rw [modByMonic_mul_right, modByMonic_mul_left, mul_assoc, ← pow_succ,
      modByMonic_mul_right]

theorem xoshiro_period (r : Rng.Xoshiro256) : Rng.advance (2 ^ 256 - 1) r = r := by
  apply packState_inj
  rw [packState_advance]
  set f := evalBinv (packState r)
  have hfLt : f < 2 ^ 256 := evalBinv_lt (packState r)
  have hEval : evalPoly f = packState r := evalPoly_evalBinv (packState_lt r)
  rw [← hEval, iterStep_evalPoly (2 ^ 256 - 1) f pow256_sub_one_lt hfLt, pow_period_one]
  have hm := natToPoly_polyMul hfLt one_lt_pow256
  have hMod : (natToPoly f * natToPoly 1) %ₘ charPoly = natToPoly f := by
    rw [natToPoly_one, mul_one, Polynomial.modByMonic_eq_self_iff charPoly_monic,
      charPoly_degree]
    exact natToPoly_degree_lt f 256 hfLt
  rw [natToPoly_inj (hm.2.trans hMod)]

private theorem evalBinv_packState_pos {r : Rng.Xoshiro256} (hr : r ≠ Rng.Xoshiro256.zero) :
    0 < evalBinv (packState r) := by
  by_contra hLe
  have hz : evalBinv (packState r) = 0 := by omega
  have hEval := evalPoly_evalBinv (packState_lt r)
  rw [hz, evalPoly_zero] at hEval
  have hZero : packState Rng.Xoshiro256.zero = 0 := by decide
  exact hr (packState_inj (hEval.symm.trans hZero.symm))

theorem xoshiro_orbit_inj (r : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero)
    {i j : Nat} (hi : i < 2 ^ 256 - 1) (hj : j < 2 ^ 256 - 1)
    (hEq : Rng.advance i r = Rng.advance j r) : i = j := by
  set f := evalBinv (packState r)
  have hfPos : 0 < f := evalBinv_packState_pos hr
  have hfLt : f < 2 ^ 256 := evalBinv_lt (packState r)
  have hEval : evalPoly f = packState r := evalPoly_evalBinv (packState_lt r)
  obtain ⟨m, _hmLt, hmPoly⟩ := poly_surj_x_pow hfPos hfLt
  have hPack := congrArg packState hEq
  have hiLt : i < 2 ^ 256 := lt_trans hi pow256_sub_one_lt
  have hjLt : j < 2 ^ 256 := lt_trans hj pow256_sub_one_lt
  have hi257 : i < 2 ^ 257 := lt_trans hiLt pow256_lt_pow257
  have hj257 : j < 2 ^ 257 := lt_trans hjLt pow256_lt_pow257
  rw [packState_advance, packState_advance, ← hEval,
    iterStep_evalPoly i f hiLt hfLt, iterStep_evalPoly j f hjLt hfLt] at hPack
  have hPolyMul : polyMul f (polyPow 2 i) = polyMul f (polyPow 2 j) :=
    evalPoly_inj
      (natToPoly_polyMul hfLt (natToPoly_polyPow 2 i hi257 two_lt_pow256).1).1
      (natToPoly_polyMul hfLt (natToPoly_polyPow 2 j hj257 two_lt_pow256).1).1
      hPack
  have hMi := (natToPoly_polyMul hfLt (natToPoly_polyPow 2 i hi257 two_lt_pow256).1).2
  have hMj := (natToPoly_polyMul hfLt (natToPoly_polyPow 2 j hj257 two_lt_pow256).1).2
  have hPi := (natToPoly_polyPow 2 i hi257 two_lt_pow256).2
  have hPj := (natToPoly_polyPow 2 j hj257 two_lt_pow256).2
  rw [hPolyMul] at hMi
  have hModEq : (natToPoly f * natToPoly (polyPow 2 i)) %ₘ charPoly =
      (natToPoly f * natToPoly (polyPow 2 j)) %ₘ charPoly := hMi.symm.trans hMj
  rw [hPi, hPj, natToPoly_two, modByMonic_mul_right, modByMonic_mul_right, hmPoly,
    modByMonic_mul_left, modByMonic_mul_left, ← pow_add, ← pow_add] at hModEq
  set N := 2 ^ 256 - 1
  have hPowPer : ∀ q : Nat, ((Polynomial.X ^ N) ^ q) %ₘ charPoly = 1 := by
    intro q
    induction q with
    | zero =>
      rw [pow_zero]
      exact (Polynomial.modByMonic_eq_self_iff charPoly_monic).mpr (by
        rw [charPoly_degree, Polynomial.degree_one]; decide)
    | succ q ih =>
      rw [pow_succ, ← modByMonic_mul_left, ih, one_mul, x_pow_period_mod]
  have reduceMod : ∀ s : Nat,
      (Polynomial.X ^ s) %ₘ charPoly = (Polynomial.X ^ (s % N)) %ₘ charPoly := by
    intro s
    have hs : s = N * (s / N) + s % N := (Nat.div_add_mod s N).symm
    conv_lhs => rw [hs, pow_add, pow_mul, ← modByMonic_mul_left, hPowPer (s / N), one_mul]
  rw [reduceMod (m + i), reduceMod (m + j)] at hModEq
  have hModSame : (m + i) % N = (m + j) % N :=
    x_pow_mod_inj (Nat.mod_lt _ pow256_sub_one_pos) (Nat.mod_lt _ pow256_sub_one_pos) hModEq
  have hDiff : i % N = j % N := Nat.ModEq.add_left_cancel' m hModSame
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hDiff
  exact hDiff

theorem xoshiro_orbit_surj (r target : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero)
    (ht : target ≠ Rng.Xoshiro256.zero) :
    ∃ d < 2 ^ 256 - 1, Rng.advance d r = target := by
  set fr := evalBinv (packState r)
  set ft := evalBinv (packState target)
  have hfrPos : 0 < fr := evalBinv_packState_pos hr
  have hftPos : 0 < ft := evalBinv_packState_pos ht
  have hfrLt : fr < 2 ^ 256 := evalBinv_lt (packState r)
  have hftLt : ft < 2 ^ 256 := evalBinv_lt (packState target)
  obtain ⟨mr, hmrLt, hmrPoly⟩ := poly_surj_x_pow hfrPos hfrLt
  obtain ⟨mt, hmtLt, hmtPoly⟩ := poly_surj_x_pow hftPos hftLt
  set N := 2 ^ 256 - 1
  let d := if mr ≤ mt then mt - mr else N + mt - mr
  have hdLt : d < N := by
    dsimp [d]
    split
    · exact Nat.lt_of_le_of_lt (Nat.sub_le mt mr) hmtLt
    · rename_i hNot
      have hGt : mt < mr := Nat.lt_of_not_ge hNot
      omega
  refine ⟨d, hdLt, ?_⟩
  apply packState_inj
  have hd256 : d < 2 ^ 256 := lt_trans hdLt pow256_sub_one_lt
  have hd257 : d < 2 ^ 257 := lt_trans hd256 pow256_lt_pow257
  rw [packState_advance, ← evalPoly_evalBinv (packState_lt r),
    ← evalPoly_evalBinv (packState_lt target), iterStep_evalPoly d fr hd256 hfrLt]
  apply congrArg evalPoly
  apply natToPoly_inj
  have hMd := (natToPoly_polyMul hfrLt (natToPoly_polyPow 2 d hd257 two_lt_pow256).1).2
  have hPd := (natToPoly_polyPow 2 d hd257 two_lt_pow256).2
  rw [hMd, hPd, natToPoly_two, modByMonic_mul_right, hmrPoly, modByMonic_mul_left, ← pow_add,
    hmtPoly]
  have hSum : mr + d = mt ∨ mr + d = N + mt := by
    dsimp [d]
    split
    · rename_i hle; exact Or.inl (Nat.add_sub_of_le hle)
    · rename_i hNot
      have hGt : mt < mr := Nat.lt_of_not_ge hNot
      have hLe : mr ≤ N + mt := Nat.le_trans (Nat.le_of_lt hmrLt) (Nat.le_add_right N mt)
      exact Or.inr (Nat.add_sub_of_le hLe)
  rcases hSum with hEq | hWrap
  · rw [hEq]
  · rw [hWrap, pow_add, ← modByMonic_mul_left, x_pow_period_mod, one_mul]

private theorem advance_add (a b : Nat) (r : Rng.Xoshiro256) :
    Rng.advance (a + b) r = Rng.advance a (Rng.advance b r) := by
  induction b generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ]
    exact ih r.next.2

def checkCalmRun : Nat → Rng.Xoshiro256 → Bool
  | 0, _ => true
  | n + 1, r => !((r.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) && checkCalmRun n r.next.2

theorem checkCalmRun_add (a b : Nat) (r : Rng.Xoshiro256) :
    checkCalmRun (a + b) r = (checkCalmRun a r && checkCalmRun b (Rng.advance a r)) := by
  induction a generalizing r with
  | zero => simp [checkCalmRun, Rng.advance]
  | succ k ih =>
    rw [Nat.succ_add, checkCalmRun, checkCalmRun, Rng.advance, Bool.and_assoc, ih r.next.2]

def checkCalmAndEnd : Nat → Rng.Xoshiro256 → Rng.Xoshiro256 → Bool
  | 0, r, target => r == target
  | n + 1, r, target =>
    !((r.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) && checkCalmAndEnd n r.next.2 target

theorem checkCalmAndEnd_spec :
    ∀ (n : Nat) (r target : Rng.Xoshiro256), checkCalmAndEnd n r target = true →
      checkCalmRun n r = true ∧ Rng.advance n r = target
  | 0, r, target, h => ⟨rfl, eq_of_beq h⟩
  | n + 1, r, target, h => by
    simp only [checkCalmAndEnd, Bool.and_eq_true] at h
    obtain ⟨hC, hR⟩ := checkCalmAndEnd_spec n r.next.2 target h.2
    simp only [checkCalmRun, Bool.and_eq_true, Rng.advance]
    exact ⟨⟨h.1, hC⟩, hR⟩

theorem checkCalmRun_spec :
    ∀ (n : Nat) (r : Rng.Xoshiro256), checkCalmRun n r = true →
      ∀ i : Nat, i < n →
        decide (((Rng.advance i r).next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false
  | 0, _, _, _, hi => by omega
  | n + 1, r, hChk, i, hi => by
    simp only [checkCalmRun, Bool.and_eq_true, Bool.not_eq_true'] at hChk
    cases i with
    | zero => exact hChk.1
    | succ k => exact checkCalmRun_spec n r.next.2 hChk.2 k (by omega)

theorem explorer_cold_rng_nonzero (count : Word.Count) (seed : UInt64) :
    (Explorer.cold count seed).rng ≠ Rng.Xoshiro256.zero :=
  Rng.seed_nonzero _

private theorem reservoir_rng {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir pending seen pick rng).2 = Rng.advance pending.length rng := by
  induction pending generalizing seen pick rng with
  | nil => rfl
  | cons action rest ih =>
    rw [reservoir_cons]
    dsimp only
    rw [ih _ _ _, Rng.nextBelow_transition, List.length_cons, advance_add]
    rfl

private theorem declared_calm_iff {count : Word.Count} (rng : Rng.Xoshiro256) :
    decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false →
      (beginExploration count declaredRate rng).1 = none ∧
      (beginExploration count declaredRate rng).2 = rng.next.2 := by
  intro hFalse
  unfold beginExploration
  dsimp only
  rw [TemporalSupport.declared_branch, hFalse, Rng.nextF64_transition]
  simp

private def remLeft {count : Word.Count} (r : Option (ExploratoryRun count)) : Nat :=
  match r with
  | none => 0
  | some run => run.remaining.val

private theorem remLeft_le {count : Word.Count} (r : Option (ExploratoryRun count)) :
    remLeft r ≤ 127 := by
  cases r with
  | none => exact Nat.zero_le 127
  | some run =>
    have hLt : run.remaining.val < 128 := run.remaining.isLt
    dsimp [remLeft]
    omega

private theorem leftToServe_remLeft_le {count : Word.Count} (r : Option (ExploratoryRun count)) :
    remLeft (leftToServe r) ≤ 127 :=
  remLeft_le (leftToServe r)

private theorem policy_candidates_len_le {count : Word.Count} (pol : PolicySnapshot count) :
    pol.candidates.length ≤ count.word.toNat := by
  rw [PolicySnapshot.candidates_def]
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_finRange])

private theorem remLeft_eq_zero_iff {count : Word.Count} (r : Option (ExploratoryRun count)) :
    r.bind ExploratoryRun.serve = none ↔ remLeft r = 0 := by
  cases r with
  | none => simp [remLeft]
  | some run =>
    change run.serve = none ↔ run.remaining.val = 0
    exact run.spent

private theorem beginExploration_rng {count : Word.Count} (rate : SwiftTd.ExploreRate)
    (rng : Rng.Xoshiro256) :
    match (beginExploration count rate rng).1 with
    | none => (beginExploration count rate rng).2 = Rng.advance 1 rng
    | some _ => (beginExploration count rate rng).2 = Rng.advance 3 rng := by
  unfold beginExploration uniformAction
  by_cases h : (!(rng.nextF64.1.less (Conversion.widen rate.value))) = true
  · simp [h, Rng.nextF64_transition, Rng.advance]
  · simp [h, Rng.nextBelow_transition, Rng.nextF64_transition, Rng.advance]

private theorem stepOver_transition {count : Word.Count} (hCount : count.word.toNat ≤ 9)
    (ex : Explorer count) (pol : PolicySnapshot count) (hEps : pol.epsilon = declaredRate)
    (hZero : ex.rng ≠ Rng.Xoshiro256.zero) :
    (ex.stepOver pol).2.rng ≠ Rng.Xoshiro256.zero ∧
      ((remLeft ex.run > 0 ∧
          (ex.stepOver pol).2.rng = ex.rng ∧
          remLeft (ex.stepOver pol).2.run < remLeft ex.run) ∨
        (ex.run.bind ExploratoryRun.serve = none ∧
          remLeft (ex.stepOver pol).2.run ≤ 127 ∧
          (∃ d, 1 ≤ d ∧ d ≤ 10 ∧ (ex.stepOver pol).2.rng = Rng.advance d ex.rng) ∧
          (decide (((ex.rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23)) = false →
            (ex.stepOver pol).2.run = none))) := by
  unfold Explorer.stepOver
  cases hSrv : ex.run.bind ExploratoryRun.serve with
  | some served =>
    have hPos : remLeft ex.run > 0 := by
      rcases ex with ⟨r, rng⟩
      cases r with
      | none => simp at hSrv
      | some run =>
        change run.serve = some served at hSrv
        have hEx := (run.serve_exact served.2 served.1 hSrv).2.2
        dsimp [remLeft]; omega
    have hDrop : remLeft (some served.2) < remLeft ex.run := by
      rcases ex with ⟨r, rng⟩
      cases r with
      | none => simp at hSrv
      | some run =>
        change run.serve = some served at hSrv
        have hEx := (run.serve_exact served.2 served.1 hSrv).2.2
        dsimp [remLeft]; omega
    exact ⟨hZero, Or.inl ⟨hPos, rfl, hDrop⟩⟩
  | none =>
    dsimp only
    rw [PolicySnapshot.drawPersistent_def]
    dsimp only
    have hRngMatch := beginExploration_rng (count := count) pol.epsilon ex.rng
    cases hB : (beginExploration count pol.epsilon ex.rng).1 with
    | some run =>
      rw [hB] at hRngMatch
      have hNz : (Explorer.mk (leftToServe (some run))
          (beginExploration count pol.epsilon ex.rng).2 : Explorer count).rng ≠
          Rng.Xoshiro256.zero := by
        change (beginExploration count pol.epsilon ex.rng).2 ≠ Rng.Xoshiro256.zero
        rw [hRngMatch]
        exact Rng.advance_nonzero 3 ex.rng hZero
      have hImp : decide (((ex.rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23)) = false →
          (Explorer.mk (leftToServe (some run))
            (beginExploration count pol.epsilon ex.rng).2 : Explorer count).run = none := by
        intro hFalse
        have hC := (declared_calm_iff (count := count) ex.rng hFalse).1
        rw [← hEps] at hC
        rw [hB] at hC
        cases hC
      refine ⟨hNz, Or.inr ⟨rfl, leftToServe_remLeft_le _,
        ⟨3, by omega, by omega, hRngMatch⟩, hImp⟩⟩
    | none =>
      rw [hB] at hRngMatch
      have hG : (pol.greedy (beginExploration count pol.epsilon ex.rng).2).2 =
          Rng.advance (pol.candidates.length + 1) ex.rng := by
        rw [PolicySnapshot.greedy_def, reservoir_rng, hRngMatch, ← advance_add]
      have hLen := Nat.le_trans (policy_candidates_len_le pol) hCount
      have hNz : (Rng.advance (pol.candidates.length + 1) ex.rng) ≠ Rng.Xoshiro256.zero :=
        Rng.advance_nonzero _ _ hZero
      dsimp only
      rw [hG]
      refine ⟨hNz, Or.inr ⟨rfl, leftToServe_remLeft_le none,
        ⟨pol.candidates.length + 1, by omega, by omega, rfl⟩, fun _ => rfl⟩⟩

private theorem drain_to_idle {count : Word.Count} (hCount : count.word.toNat ≤ 9)
    (ex : Nat → Explorer count)
    (hStep : ∀ t, ∃ pol : PolicySnapshot count,
      pol.epsilon = declaredRate ∧ ex (t + 1) = ((ex t).stepOver pol).2) :
    ∀ (r t : Nat), remLeft (ex t).run = r → (ex t).rng ≠ Rng.Xoshiro256.zero →
      ∃ tIdle ≥ t,
        (ex tIdle).run.bind ExploratoryRun.serve = none ∧ (ex tIdle).rng = (ex t).rng
  | r, t, hR, hNz => by
    by_cases h0 : r = 0
    · refine ⟨t, le_refl t, (remLeft_eq_zero_iff (ex t).run).mpr (by omega), rfl⟩
    · obtain ⟨pol, hEps, hEq⟩ := hStep t
      have hTr := stepOver_transition hCount (ex t) pol hEps hNz
      rw [← hEq] at hTr
      rcases hTr.2 with ⟨_, hRng, hDrop⟩ | ⟨hSrv, _, _, _⟩
      · have hr' : remLeft (ex (t + 1)).run < r := by omega
        obtain ⟨tIdle, htGe, hIdleSrv, hIdleRng⟩ :=
          drain_to_idle hCount ex hStep (remLeft (ex (t + 1)).run) (t + 1) rfl hTr.1
        exact ⟨tIdle, by omega, hIdleSrv, hIdleRng.trans hRng⟩
      · have : remLeft (ex t).run = 0 := (remLeft_eq_zero_iff _).mp hSrv
        omega
  termination_by r => r

private theorem greedy_from_small_gen {count : Word.Count} (hCount : count.word.toNat ≤ 9)
    (r : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero) (K : Nat)
    (hCalm : ∀ i : Fin (10 * K + 10),
      decide (((Rng.advance i.val r).next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false)
    (ex : Nat → Explorer count)
    (hStep : ∀ t, ∃ pol : PolicySnapshot count,
      pol.epsilon = declaredRate ∧ ex (t + 1) = ((ex t).stepOver pol).2)
    (t0 p0 : Nat) (hp0 : p0 < 10) (hSrv0 : (ex t0).run.bind ExploratoryRun.serve = none)
    (hRng0 : (ex t0).rng = Rng.advance p0 r) :
    ∀ j ≤ K, ∃ pj ≤ p0 + 10 * j,
      (ex (t0 + j)).run.bind ExploratoryRun.serve = none ∧
      (ex (t0 + j)).rng = Rng.advance pj r := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨p0, by omega, hSrv0, hRng0⟩
  | succ k ih =>
    intro hkLe
    obtain ⟨pk, hpkLe, hSrvK, hRngK⟩ := ih (by omega)
    have hpkBound : pk < 10 * K + 10 := by omega
    have hCalmK : decide (((ex (t0 + k)).rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) =
        false := by
      rw [hRngK]
      exact hCalm ⟨pk, hpkBound⟩
    have hNz : (ex (t0 + k)).rng ≠ Rng.Xoshiro256.zero := by
      rw [hRngK]; exact Rng.advance_nonzero pk r hr
    obtain ⟨pol, hEps, hEq⟩ := hStep (t0 + k)
    have hTr := stepOver_transition hCount (ex (t0 + k)) pol hEps hNz
    rw [← hEq] at hTr
    rcases hTr.2 with ⟨hPos, _, _⟩ | ⟨_, _, ⟨d, hd1, hd10, hdRng⟩, hImp⟩
    · have : remLeft (ex (t0 + k)).run = 0 := (remLeft_eq_zero_iff _).mp hSrvK
      omega
    · have hRunNone : (ex (t0 + k + 1)).run = none := hImp hCalmK
      have hSrvNext : (ex (t0 + k + 1)).run.bind ExploratoryRun.serve = none := by
        simp [hRunNone]
      refine ⟨pk + d, by omega, hSrvNext, ?_⟩
      rw [← Nat.add_assoc, hdRng, hRngK, ← advance_add, Nat.add_comm d pk]

private theorem drain_and_greedy_from_small_gen {count : Word.Count}
    (hCount : count.word.toNat ≤ 9) (r : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero)
    (K : Nat)
    (hCalm : ∀ i : Fin (10 * K + 10),
      decide (((Rng.advance i.val r).next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false)
    (ex : Nat → Explorer count)
    (hStep : ∀ t, ∃ pol : PolicySnapshot count,
      pol.epsilon = declaredRate ∧ ex (t + 1) = ((ex t).stepOver pol).2)
    (t p : Nat) (hp : p < 10) (hRng : (ex t).rng = Rng.advance p r) :
    ∃ tStart ≥ t, ∀ j < K,
      (ex (tStart + j)).run.bind ExploratoryRun.serve = none ∧
      decide (((ex (tStart + j)).rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false := by
  have hNz : (ex t).rng ≠ Rng.Xoshiro256.zero := by
    rw [hRng]; exact Rng.advance_nonzero p r hr
  obtain ⟨tIdle, htGe, hSrvIdle, hRngIdle⟩ :=
    drain_to_idle hCount ex hStep (remLeft (ex t).run) t rfl hNz
  have hIdleExact : (ex tIdle).rng = Rng.advance p r := hRngIdle.trans hRng
  refine ⟨tIdle, htGe, fun j hj => ?_⟩
  obtain ⟨pj, hpjLe, hSrvJ, hRngJ⟩ := greedy_from_small_gen
    hCount r hr K hCalm ex hStep tIdle p hp hSrvIdle hIdleExact j (by omega)
  have hpjBound : pj < 10 * K + 10 := by omega
  refine ⟨hSrvJ, ?_⟩
  rw [hRngJ]
  exact hCalm ⟨pj, hpjBound⟩

private def rngPhi {count : Word.Count} (p : Fin (2 ^ 256 - 1)) (ex : Explorer count) : Nat :=
  128 * ((2 ^ 256 - 1) - 1 - p.val) + remLeft ex.run

private theorem phi_drop_step {R p d remNew : Nat} (hp : p < R) (hd : 1 ≤ d)
    (hWrap : p + d < R) (hRem : remNew ≤ 127) :
    128 * (R - 1 - (p + d)) + remNew < 128 * (R - 1 - p) + 0 := by omega

private theorem wrap_lt_10 {R p d : Nat} (hp : p < R) (hd : d ≤ 10) (hNot : ¬ p + d < R) :
    p + d - R < 10 := by omega

private theorem wrap_add_eq {R p d : Nat} (hNot : ¬ p + d < R) :
    p + d = (p + d - R) + R := by omega

private theorem greedy_from_pos_gen {count : Word.Count} (hCount : count.word.toNat ≤ 9)
    (r : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero) (K : Nat)
    (hCalm : ∀ i : Fin (10 * K + 10),
      decide (((Rng.advance i.val r).next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false)
    (ex : Nat → Explorer count)
    (hStep : ∀ t, ∃ pol : PolicySnapshot count,
      pol.epsilon = declaredRate ∧ ex (t + 1) = ((ex t).stepOver pol).2) :
    ∀ (phi t : Nat) (p : Fin (2 ^ 256 - 1)),
      rngPhi p (ex t) ≤ phi → (ex t).rng = Rng.advance p.val r →
      ∃ tStart ≥ t, ∀ j < K,
        (ex (tStart + j)).run.bind ExploratoryRun.serve = none ∧
        decide (((ex (tStart + j)).rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false
  | phi, t, p, hPhi, hRng => by
    by_cases hp10 : p.val < 10
    · exact drain_and_greedy_from_small_gen hCount r hr K hCalm ex hStep t p.val hp10 hRng
    · have hNz : (ex t).rng ≠ Rng.Xoshiro256.zero := by
        rw [hRng]; exact Rng.advance_nonzero p.val r hr
      obtain ⟨pol, hEps, hEq⟩ := hStep t
      have hTr := stepOver_transition hCount (ex t) pol hEps hNz
      rw [← hEq] at hTr
      rcases hTr.2 with ⟨_, hRngEq, hDrop⟩ | ⟨hSrv, hRemLe, ⟨d, hd1, hd10, hAdv⟩, _⟩
      · have hPhiDrop : rngPhi p (ex (t + 1)) < phi := by
          dsimp only [rngPhi] at hPhi ⊢
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hDrop _) hPhi
        obtain ⟨tS, htSGe, htS⟩ :=
          greedy_from_pos_gen hCount r hr K hCalm ex hStep (rngPhi p (ex (t + 1))) (t + 1) p
            (le_refl _) (hRngEq.trans hRng)
        exact ⟨tS, by omega, htS⟩
      · have hRem0 : remLeft (ex t).run = 0 := (remLeft_eq_zero_iff _).mp hSrv
        have hRngNext : (ex (t + 1)).rng = Rng.advance (p.val + d) r := by
          rw [hAdv, hRng, ← advance_add, Nat.add_comm d p.val]
        by_cases hWrap : p.val + d < 2 ^ 256 - 1
        · let p' : Fin (2 ^ 256 - 1) := ⟨p.val + d, hWrap⟩
          have hPhiDrop : rngPhi p' (ex (t + 1)) < phi := by
            dsimp only [rngPhi, p'] at hPhi ⊢
            rw [hRem0] at hPhi
            exact Nat.lt_of_lt_of_le (phi_drop_step p.isLt hd1 hWrap hRemLe) hPhi
          obtain ⟨tS, htSGe, htS⟩ :=
            greedy_from_pos_gen hCount r hr K hCalm ex hStep (rngPhi p' (ex (t + 1)))
              (t + 1) p' (le_refl _) hRngNext
          exact ⟨tS, by omega, htS⟩
        · let w := p.val + d - (2 ^ 256 - 1)
          have hw10 : w < 10 := wrap_lt_10 p.isLt hd10 hWrap
          have hRngWrap : (ex (t + 1)).rng = Rng.advance w r := by
            rw [hRngNext, wrap_add_eq hWrap, advance_add, xoshiro_period]
          obtain ⟨tS, htSGe, htS⟩ :=
            drain_and_greedy_from_small_gen hCount r hr K hCalm ex hStep (t + 1) w hw10 hRngWrap
          exact ⟨tS, by omega, htS⟩
  termination_by phi => phi

theorem consecutive_greedy_of_calm {count : Word.Count} (hCount : count.word.toNat ≤ 9)
    (r : Rng.Xoshiro256) (hr : r ≠ Rng.Xoshiro256.zero) (K : Nat)
    (hCalm : ∀ i : Fin (10 * K + 10),
      decide (((Rng.advance i.val r).next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false)
    (ex : Nat → Explorer count) (hZero : (ex 0).rng ≠ Rng.Xoshiro256.zero)
    (hStep : ∀ t, ∃ pol : PolicySnapshot count,
      pol.epsilon = declaredRate ∧ ex (t + 1) = ((ex t).stepOver pol).2)
    (tMin : Nat) :
    ∃ tStart ≥ tMin, ∀ j < K,
      (ex (tStart + j)).run.bind ExploratoryRun.serve = none ∧
      decide (((ex (tStart + j)).rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) = false := by
  have hNzAll : ∀ k : Nat, (ex k).rng ≠ Rng.Xoshiro256.zero := by
    intro k
    induction k with
    | zero => exact hZero
    | succ m ih =>
      obtain ⟨pol, hEps, hEq⟩ := hStep m
      rw [hEq]
      exact (stepOver_transition hCount (ex m) pol hEps ih).1
  obtain ⟨p, hpLt, hAdv⟩ := xoshiro_orbit_surj r (ex tMin).rng hr (hNzAll tMin)
  let pFin : Fin (2 ^ 256 - 1) := ⟨p, hpLt⟩
  exact greedy_from_pos_gen hCount r hr K hCalm ex hStep (rngPhi pFin (ex tMin)) tMin pFin
    (le_refl _) hAdv.symm

theorem greedyFresh_action_mem {interface : Interface} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {planning : PlanningSelection}
    (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (percept : Percept interface)
    (unserved : (explorerOf agent.control).run.bind ExploratoryRun.serve = none)
    (calm : decide (((explorerOf agent.control).rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) =
      false)
    (hNe : (agent.control.runtime.lifecycle.consumers.control.snapshot
      (agent.choose .learnThenAct percept).features declaredRate).candidates ≠ []) :
    let snap := agent.control.runtime.lifecycle.consumers.control.snapshot
      (agent.choose .learnThenAct percept).features declaredRate
    (agent.act percept).2.action ∈ snap.candidates := by
  intro snap
  obtain ⟨hAct, _⟩ := act_draws agent primitive declared percept
  have hCalmBegin :
      (beginExploration interface.actions snap.epsilon
        (explorerOf agent.control).rng).1 = none := by
    change (beginExploration interface.actions declaredRate
      (explorerOf agent.control).rng).1 = none
    exact (declared_calm_iff _ calm).1
  rw [hAct, Explorer.stepOver_greedy _ _ unserved hCalmBegin, PolicySnapshot.greedy_def]
  cases hC : snap.candidates with
  | nil => exact absurd hC hNe
  | cons c cs => exact reservoir_nonempty c cs _ _

end AcornVerif.CurrentXoshiroPeriod
