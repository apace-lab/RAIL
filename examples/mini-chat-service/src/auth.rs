// Authentication: password credentials (real argon2) plus a bearer token that
// carries the authenticated subject on every later request.
use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    User,
    Admin,
}

#[derive(Debug, Clone)]
pub struct User {
    pub id: u64,
    pub username: String,
    pub password_hash: String,
    pub role: Role,
}

#[derive(Debug, Clone)]
pub struct Session {
    pub user_id: u64,
    pub username: String,
    pub role: Role,
}

pub fn hash_password(password: &str) -> String {
    let salt = SaltString::generate(&mut OsRng);
    Argon2::default()
        .hash_password(password.as_bytes(), &salt)
        .expect("argon2 hashing failed")
        .to_string()
}

pub fn verify_password(password: &str, password_hash: &str) -> bool {
    let Ok(parsed) = PasswordHash::new(password_hash) else {
        return false;
    };
    Argon2::default()
        .verify_password(password.as_bytes(), &parsed)
        .is_ok()
}

// Bearer-token authentication. `jsonwebtoken` is a deterministic stand-in for the
// real crate so the example runs under MadSim; CRUX matches jsonwebtoken::decode
// (authentication) and takes its first argument, the token, as the request
// principal. (argon2's verify_password is the credential check; the principal is
// established here, per request.)
pub mod jsonwebtoken {
    pub struct DecodingKey;
    pub struct Validation;

    pub struct Claims {
        pub sub: String,
    }

    pub struct TokenData<T> {
        pub claims: T,
    }

    #[inline(never)]
    pub fn decode(
        token: &str,
        _key: &DecodingKey,
        _validation: &Validation,
    ) -> Result<TokenData<Claims>, ()> {
        if token.is_empty() {
            return Err(());
        }
        Ok(TokenData {
            claims: Claims {
                sub: token.to_string(),
            },
        })
    }
}
