// The LLM endpoint. `async_openai` is a deterministic stand-in for the real SDK;
// CRUX matches the call by name (async_openai::chat::Chat::create) and marks its
// result as a per-user access node.
pub mod async_openai {
    pub struct Client;

    impl Client {
        pub fn new() -> Self {
            Client
        }
        pub fn chat(&self) -> chat::Chat {
            chat::Chat
        }
    }

    pub mod chat {
        pub struct Chat;

        impl Chat {
            #[inline(never)]
            pub fn create(&self, request: &str) -> String {
                format!("(answer for '{request}')")
            }
        }
    }
}
