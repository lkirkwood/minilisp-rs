use std::collections::{HashMap, hash_map::Entry};

use anyhow::{Result, bail};

use crate::ast::BoxExpr;

#[derive(Default)]
/// Context the compiler needs to carry throughout the process.
pub struct Context {
    /// Identifiers mapped to an address.
    /// Multiple addresses may be present to allow shadowing.
    bindings: HashMap<String, Vec<String>>,
    /// Current offset from base pointer.
    stack_offset: usize,
    /// Number of labels so far created.
    labels: usize,
}

/// Contains a new context for a lambda.
pub struct LambdaContext {
    /// Instructions to run before using the context.
    pub prologue: String,
    /// The context itself.
    pub context: Context,
    /// Instructions to run after using the context.
    pub epilogue: String,
}

impl Context {
    /// Allocate `num_bytes` and return the offset address relative to the
    /// current stack base pointer.
    pub fn stack_alloc(&mut self, num_bytes: usize) -> String {
        self.stack_offset += num_bytes;
        format!("[rbp - {}]", self.stack_offset)
    }

    pub fn stack_free(&mut self, num_bytes: usize) {
        self.stack_offset -= num_bytes
    }

    /// Allocate 8 bytes on the stack and bind `ident` to them.
    /// Return their location in memory.
    pub fn bind(&mut self, ident: String) -> String {
        let addr = self.stack_alloc(8);
        match self.bindings.entry(ident) {
            Entry::Occupied(mut entry) => entry.get_mut().push(addr.clone()),
            Entry::Vacant(entry) => {
                entry.insert(vec![addr.clone()]);
            }
        }
        addr
    }

    /// Unbind the innermost binding for `ident`.
    pub fn unbind(&mut self, ident: &str) -> Result<()> {
        if let Some(addrs) = self.bindings.get_mut(ident)
            && !addrs.is_empty()
        {
            addrs.pop();
            return Ok(());
        }
        bail!("Tried to unbind unbound identifier {ident}")
    }

    /// Get the offset address `ident` is bound to.
    pub fn get(&self, ident: &str) -> Result<String> {
        if let Some(addrs) = self.bindings.get(ident)
            && !addrs.is_empty()
        {
            return Ok(addrs.last().unwrap().clone());
        }
        bail!("Tried to use an unbound identifier: {ident}");
    }

    /// Create a new globally unique label.
    pub fn new_label(&mut self) -> String {
        let label = format!("label_{}", self.labels);
        self.labels += 1;
        label
    }
}
