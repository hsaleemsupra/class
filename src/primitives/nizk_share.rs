use std::ops::{Add, Mul};
use curv::arithmetic::{Converter, Modulo};
use curv::BigInt;
use curv::cryptographic_primitives::hashing::{Digest, DigestExt};
use curv::elliptic::curves::{Point, Scalar, Secp256k1};
use num_traits::{One, Zero};
use sha2::Sha256;
use crate::primitives::cl_dl_public_setup::{Ciphertext, CLGroup, PK};
use super::cl_dl_public_setup::SECURITY_PARAMETER;
use crate::{BinaryQF, pari_init};

/// Domain separators for the zk proof of sharing
const DOMAIN_PROOF_OF_SHARING_INSTANCE: &str = "crypto-classgroup-dkg-zk-proof-of-sharing-instance";
const DOMAIN_PROOF_OF_SHARING_CHALLENGE: &str = "crypto-classgroup-dkg-zk-proof-of-sharing-challenge";

/// Zero-knowledge proof of sharing.
#[derive(Clone, Debug)]
pub struct ZkProofSharing {
    pub ff: Point<Secp256k1>,
    pub aa: Point<Secp256k1>,
    pub yy: BinaryQF,
    pub z_r: BigInt,
    pub z_alpha: BigInt,
}

pub struct SharingInstance {
    pub g1_gen: Point<Secp256k1>,
    pub g: Point<Secp256k1>,
    pub public_keys: Vec<PK>,
    pub public_coefficients: Vec<Point<Secp256k1>>,
    pub g_r: Point<Secp256k1>,
    pub ciphertexts: Vec<Ciphertext>,
}

pub struct Witness {
    pub r: BigInt,
    pub s: Vec<BigInt>,
}

struct FirstMoveSharing {
    pub ff: Point<Secp256k1>,
    pub aa: Point<Secp256k1>,
    pub yy: BinaryQF,
}

impl From<&ZkProofSharing> for FirstMoveSharing {
    fn from(proof: &ZkProofSharing) -> Self {
        Self {
            ff: proof.ff.to_owned(),
            aa: proof.aa.to_owned(),
            yy: proof.yy.to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkProofSharingError {
    InvalidProof,
    InvalidInstance,
}

impl SharingInstance {
    // Computes the hash of the instance.
    pub fn hash_to_scalar(&self) -> BigInt {

        let mut hash256 = Sha256::new()
            .chain(DOMAIN_PROOF_OF_SHARING_INSTANCE)
            .chain_point(&self.g1_gen)
            .chain_point(&self.g);

        for pk in &self.public_keys{
            hash256 = hash256.chain(pk.0.to_bytes());
        }

        hash256 = hash256.chain_points(&self.public_coefficients);
        hash256 = hash256.chain_point(&self.g_r);

        for cc in &self.ciphertexts{
            hash256 = hash256.chain(cc.c1.to_bytes());
            hash256 = hash256.chain(cc.c2.to_bytes());
        }

        let output = hash256.finalize();

        BigInt::from_bytes(&output[..SECURITY_PARAMETER / 8])

    }

    pub fn check_instance(&self) -> Result<(), ZkProofSharingError> {
        if self.public_keys.is_empty() || self.public_coefficients.is_empty() {
            return Err(ZkProofSharingError::InvalidInstance);
        };
        if self.public_keys.len() != self.ciphertexts.len() {
            return Err(ZkProofSharingError::InvalidInstance);
        };
        Ok(())
    }
}

fn sharing_proof_challenge(hashed_instance: &BigInt, first_move: &FirstMoveSharing) -> BigInt {

    let hash256 = Sha256::new()
        // hash the statement i.e. the discrete log of Q is encrypted in (c1,c2) under encryption key h.
        .chain(DOMAIN_PROOF_OF_SHARING_CHALLENGE)
        .chain_bigint(&hashed_instance)
        .chain_point(&first_move.ff)
        .chain_point(&first_move.aa)
        .chain(&first_move.yy.to_bytes())
        .finalize();

    BigInt::from_bytes(&hash256[..SECURITY_PARAMETER / 8])
}

pub fn prove_sharing(group: &CLGroup, witness: &Witness, instance: &SharingInstance) -> ZkProofSharing {

    instance
        .check_instance()
        .expect("The sharing proof instance is invalid");

    unsafe { pari_init(100000000, 2) };

    let alpha_fe = Scalar::<Secp256k1>::random();
    let alpha = alpha_fe.to_bigint();

    let rho_fe = Scalar::<Secp256k1>::random();
    let rho = rho_fe.to_bigint();

    let ff =  &instance.g1_gen * &rho_fe;
    let aa =  &instance.g * &alpha_fe;

    let x = instance.hash_to_scalar();

    let mut x_pows: Vec<BigInt> = Vec::new();
    x_pows.push(x.clone());

    for i in 1..instance.public_keys.len(){
        x_pows.push(BigInt::mod_mul(&x,&x_pows.get(i-1).unwrap(), Scalar::<Secp256k1>::group_order()));
    }

    let mut acc_pk = instance.public_keys[0].0.clone();
    acc_pk = acc_pk.exp(&x_pows[0]);

    for i in 1..instance.public_keys.len(){

        let hi = instance.public_keys[i].0.clone();

        acc_pk = hi.exp(&x_pows[i])
                    .compose(&acc_pk)
                    .reduce();
    }

    let f_aa = BinaryQF::expo_f(
        Scalar::<Secp256k1>::group_order(),
        &group.delta_q,
        &alpha,
    );

    let yy = acc_pk.exp(&rho).compose(&f_aa).reduce();

    let first_move = FirstMoveSharing {
        ff,
        aa,
        yy,
    };

    // Second move (verifier's challenge)
    // x' = oracle(x, F, A, Y)
    let x_challenge = sharing_proof_challenge(&x, &first_move);

    // Third move (prover)
    // z_r = r * x' + rho mod p
    // z_alpha = x' * sum [s_i*x^i | i <- [1..n]] + alpha mod p

    let z_r = &witness.r * &x_challenge + &rho;

    let mut z_alpha = witness.s.iter()
        .rev()
        .fold(BigInt::zero(), |mut acc, scalar| {
            acc = BigInt::mod_add(&acc, &scalar, Scalar::<Secp256k1>::group_order());
            BigInt::mod_mul(&acc, &x, Scalar::<Secp256k1>::group_order())
        });

    z_alpha = BigInt::mod_mul(&z_alpha, &x_challenge, Scalar::<Secp256k1>::group_order());
    z_alpha = BigInt::mod_add(&z_alpha, &alpha, Scalar::<Secp256k1>::group_order());


    ZkProofSharing {
        ff: first_move.ff,
        aa: first_move.aa,
        yy: first_move.yy,
        z_r,
        z_alpha,
    }
}


pub fn verify_sharing(group: &CLGroup,
    instance: &SharingInstance,
    nizk: &ZkProofSharing
) -> Result<(), ZkProofSharingError> {
    unsafe { pari_init(100000000, 2) };
    instance.check_instance()?;
    // Hash of Instance
    // x = oracle(instance)
    let x = instance.hash_to_scalar();

    let first_move = FirstMoveSharing::from(nizk);
    // Verifier's challenge
    // x' = oracle(x, F, A, Y)
    let x_challenge = sharing_proof_challenge(&x, &first_move);

    // First verification equation
    // R^x' * F == g_1^z_r
    let mut lhs = instance.g_r.clone();
    lhs = &lhs *  Scalar::<Secp256k1>::from(x_challenge.clone());
    lhs = &lhs +  &first_move.ff;

    let mut rhs = instance.g1_gen.clone();
    rhs = rhs.mul(&Scalar::<Secp256k1>::from(nizk.z_r.clone()));

    if !lhs.eq(&rhs) {
        return Err(ZkProofSharingError::InvalidProof);
    }

    // Second verification equation
    // Verify: product [A_k ^ sum [i^k * x^i | i <- [1..n]] | k <- [0..t-1]]^x' * A
    // == g_2^z_alpha
    let mut kbig = BigInt::zero();
    let one = BigInt::one();
    let mut lhs = Point::<Secp256k1>::zero();
    instance.public_coefficients.iter().for_each(|aa_k| {
        let mut acc = BigInt::zero();
        let mut xpow = x.clone(); // David: for x^i
        let mut ibig = BigInt::one(); // David: for i (in i^k)
        instance.public_keys.iter().for_each(|_| {
            let tmp = BigInt::mod_mul(&BigInt::mod_pow(&ibig, &kbig, &Scalar::<Secp256k1>::group_order())
                                      ,&xpow
                                      , &Scalar::<Secp256k1>::group_order());
            acc = BigInt::mod_add(&acc, &tmp, &Scalar::<Secp256k1>::group_order());
            xpow = BigInt::mod_mul(&xpow, &x, &Scalar::<Secp256k1>::group_order());
            ibig = BigInt::mod_add(&ibig, &BigInt::one(), &Scalar::<Secp256k1>::group_order());
        });

        lhs = &lhs + (aa_k * Scalar::<Secp256k1>::from(acc));
        kbig = BigInt::mod_add(&kbig, &one, &Scalar::<Secp256k1>::group_order());

    });

    lhs = &lhs *  Scalar::<Secp256k1>::from(x_challenge.clone());
    lhs = lhs.add(&nizk.aa);

    let mut rhs = instance.g.clone();
    rhs = rhs.mul(Scalar::<Secp256k1>::from(nizk.z_alpha.clone()));

    if !lhs.eq(&rhs) {
        return Err(ZkProofSharingError::InvalidProof);
    }

    // Third verification equation
    // LHS = product [C_i ^ x^i | i <- [1..n]]^x' * Y
    // RHS = product [y_i ^ x^i | i <- 1..n]^z_r * g_1^z_alpha


    let mut x_pows: Vec<BigInt> = Vec::new();
    x_pows.push(x.clone());
    for i in 1..instance.public_keys.len(){
        x_pows.push(BigInt::mod_mul(&x,&x_pows[i-1], &Scalar::<Secp256k1>::group_order()));
    }

    let mut lhs = instance.ciphertexts[0].c2.clone();
    lhs = lhs.exp(&x_pows[0]);
    for i in 1..instance.ciphertexts.len(){
        let ci = &instance.ciphertexts[i].c2;
        lhs = ci.exp(&x_pows[i])
            .compose(&lhs)
            .reduce();
    }
    lhs = lhs.exp(&x_challenge).compose(&nizk.yy).reduce();

    let mut rhs = instance.public_keys[0].0.clone();
    rhs = rhs.exp(&x_pows[0]);
    for i in 1..instance.public_keys.len(){

        let hi = &instance.public_keys[i].0;

        rhs = hi.exp(&x_pows[i])
            .compose(&rhs)
            .reduce();
    }

    let f_z_alpha = BinaryQF::expo_f(
        &Scalar::<Secp256k1>::group_order(),
        &group.delta_q,
        &nizk.z_alpha,
    );
    rhs = rhs.exp(&nizk.z_r).compose(&f_z_alpha).reduce();

    if lhs != rhs {
        return Err(ZkProofSharingError::InvalidProof);
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use curv::elliptic::curves::secp256_k1::hash_to_curve::generate_random_point;
    use crate::primitives::cl_dl_public_setup::{encrypt_predefined_randomness, SK};
    use super::*;

    const seed: &str =  "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848";

    fn setup_sharing_instance_and_witness(group: &CLGroup) -> (Point<Secp256k1>, Point<Secp256k1>,Vec<PK>, Vec<Point<Secp256k1>>, Point<Secp256k1>, Vec<Ciphertext>, BigInt, Vec<BigInt>) {
        let g1 = Point::<Secp256k1>::generator().to_point();
        //let g = get_nidkg_zk_share_g(&"test-dig".to_string());

        let hash256 = Sha256::new()
            .chain("test-class-dkg")
            .finalize();

        let g = generate_random_point(&*hash256);

        let mut pk = Vec::new();
        let mut a = Vec::new();
        let mut aa = Vec::new();
        let node_count = 28;
        let threshold = 28;

        for _i in 1..node_count + 1 {
            let (_, public_key) = group.keygen();
            pk.push(public_key);
        }
        for _i in 0..threshold {
            let apow = Scalar::<Secp256k1>::random();
            a.push(apow.clone());
            aa.push(g.clone() * apow.clone());
        }

        let r  = Scalar::<Secp256k1>::random().to_bigint();

        let rr = g1.clone() * Scalar::<Secp256k1>::from(&r);
        let mut s = Vec::new();
        // s = [sum [a_k ^ i^k | (a_k, k) <- zip a [0..t-1]] | i <- [1..n]]
        for i in 1..node_count + 1 {
            let ibig = BigInt::from(i);
            let mut ipow = BigInt::from(1);
            let mut acc = BigInt::from(0);
            for ak in &a {
                acc = acc + (ak.to_bigint()*&ipow);
                ipow = ipow * &ibig;
            }
            s.push(acc);
        }

        let mut cc:Vec<Ciphertext> = Vec::new();

        for i in 0..s.len(){
            cc.push(encrypt_predefined_randomness(group,pk.get(i).unwrap(),&Scalar::<Secp256k1>::from(s.get(i).unwrap()),&SK::from(r.clone())));
        }

        (g1, g, pk, aa, rr, cc, r, s.clone())
    }


    #[test]
    fn sharing_nizk_should_verify() {

        let group = CLGroup::new_from_setup(&1600, &BigInt::from_str_radix(seed, 10).unwrap());
        let (g1_gen, g, pk, aa, rr, cc, r, s)
            = setup_sharing_instance_and_witness(&group);

        let instance = SharingInstance {
            g1_gen: g1_gen,
            g: g,
            public_keys: pk.clone(),
            public_coefficients: aa,
            g_r: rr,
            ciphertexts: cc,
        };


        let witness = Witness {
            r: r.clone(),
            s: s.clone(),
        };

        let sharing_proof = prove_sharing(&group, &witness, &instance);

        assert_eq!(
            Ok(()),
            verify_sharing(&group, &instance, &sharing_proof),
            "verify_sharing verifies NIZK proof"
        );
    }

    #[test]
    #[should_panic(expected = "The sharing proof instance is invalid: InvalidInstance")]
    fn sharing_prover_should_panic_on_empty_coefficients() {
        let group = CLGroup::new_from_setup(&1600, &BigInt::from_str_radix(seed, 10).unwrap());
        let (g1_gen, g, pk, _aa, rr, cc, r, s) = setup_sharing_instance_and_witness(&group);

        let instance = SharingInstance {
            g1_gen: g1_gen,
            g: g,
            public_keys: pk.clone(),
            public_coefficients: vec![],
            g_r: rr,
            ciphertexts: cc,
        };

        let witness = Witness {
            r: r.clone(),
            s: s.clone(),
        };
        let _panic_one = prove_sharing(&group, &witness, &instance);
    }

    #[test]
    #[should_panic(expected = "The sharing proof instance is invalid: InvalidInstance")]
    fn sharing_prover_should_panic_on_invalid_instance() {
        let group = CLGroup::new_from_setup(&1600, &BigInt::from_str_radix(seed, 10).unwrap());
        let (g1_gen, g, mut pk, aa, rr, cc, r, s) = setup_sharing_instance_and_witness(&group);
        pk.push(PK(group.gq.clone()));
        let instance = SharingInstance {
            g1_gen: g1_gen,
            g: g,
            public_keys: pk.clone(),
            public_coefficients: aa,
            g_r: rr,
            ciphertexts: cc,
        };

        let witness = Witness {
            r: r.clone(),
            s: s.clone(),
        };
        let _panic_one = prove_sharing(&group, &witness, &instance);
    }

    #[test]
    fn sharing_nizk_should_fail_on_invalid_instance() {
        let group = CLGroup::new_from_setup(&1600, &BigInt::from_str_radix(seed, 10).unwrap());
        let (g1_gen, g, mut pk, aa, rr, cc, r, s) = setup_sharing_instance_and_witness(&group);

        let instance = SharingInstance {
            g1_gen: g1_gen.clone(),
            g: g.clone(),
            public_keys: pk.clone(),
            public_coefficients: aa.clone(),
            g_r: rr.clone(),
            ciphertexts: cc.clone(),
        };
        pk.push(PK(group.gq.clone()));
        let invalid_instance = SharingInstance {
            g1_gen: g1_gen,
            g: g.clone(),
            public_keys: pk.clone(),
            public_coefficients: aa.clone(),
            g_r: rr.clone(),
            ciphertexts: cc.clone(),
        };

        let witness = Witness {
            r: r.clone(),
            s: s.clone(),
        };
        let _panic_one = prove_sharing(&group, &witness, &instance);

        let sharing_proof = prove_sharing(&group, &witness, &instance);
        assert_eq!(
            Err(ZkProofSharingError::InvalidInstance),
            verify_sharing(&group, &invalid_instance, &sharing_proof),
            "verify_sharing fails on invalid instance"
        );
    }


    #[test]
    fn sharing_nizk_should_fail_on_invalid_proof() {
        let group = CLGroup::new_from_setup(&1600, &BigInt::from_str_radix(seed, 10).unwrap());
        let (g1_gen, g, pk, aa, rr, cc, r, s) = setup_sharing_instance_and_witness(&group);

        let instance = SharingInstance {
            g1_gen: g1_gen.clone(),
            g: g.clone(),
            public_keys: pk.clone(),
            public_coefficients: aa.clone(),
            g_r: rr.clone(),
            ciphertexts: cc.clone(),
        };

        let witness = Witness {
            r: r.clone(),
            s: s.clone(),
        };
        let _panic_one = prove_sharing(&group, &witness, &instance);

        let sharing_proof = prove_sharing(&group, &witness, &instance);
        let invalid_proof = ZkProofSharing {
            ff: sharing_proof.ff,
            aa: sharing_proof.aa,
            yy: group.gq.clone(),
            z_r: sharing_proof.z_r,
            z_alpha: sharing_proof.z_alpha,
        };
        assert_eq!(
            Err(ZkProofSharingError::InvalidProof),
            verify_sharing(&group, &instance, &invalid_proof),
            "verify_sharing fails on invalid proof"
        );
    }

}