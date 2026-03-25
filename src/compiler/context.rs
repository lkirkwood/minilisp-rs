use std::collections::{HashMap, hash_map::Entry};

use anyhow::{Result, bail};

#[derive(Default)]
/// Context the compiler needs to carry throughout the process.
pub struct Context {
    /// Identifiers mapped to an offset from the base pointer, at which they are stored.
    bindings: HashMap<String, Vec<usize>>,
    /// Current offset from base pointer.
    current_offset: usize,
    /// Number of labels so far created.
    labels: usize,
    /// Base addresses that bindings are relative to. If empty, use `rbp`.
    base_addrs: Vec<String>,
}

impl Context {
    /// Return the current base address.
    pub fn base_addr(&self) -> &str {
        if self.base_addrs.is_empty() {
            "rbp"
        } else {
            self.base_addrs.last().unwrap()
        }
    }

    /// Allocate `num_bytes` and return the offset.
    fn stack_allocate(&mut self, num_bytes: usize) -> usize {
        self.current_offset += num_bytes;
        self.current_offset
    }

    /// Return an offset address relative to the current stack base pointer.
    fn offset_addr(&self, offset: usize) -> String {
        format!("[{} - {}]", self.base_addr(), offset)
    }

    /// Allocate `num_bytes` and return the offset address relative to the
    /// current stack base pointer. Roughly shorthand for:
    /// `ctx.offset_addr(ctx.stack_allocate(num_bytes))`.
    pub fn stack_addr(&mut self, num_bytes: usize) -> String {
        let offset = self.stack_allocate(num_bytes);
        self.offset_addr(offset)
    }

    /// Allocate 8 bytes on the stack and bind `ident` to them.
    /// Return their location in memory.
    pub fn bind(&mut self, ident: String) -> String {
        let offset = self.stack_allocate(8);
        match self.bindings.entry(ident) {
            Entry::Occupied(mut entry) => entry.get_mut().push(offset),
            Entry::Vacant(entry) => {
                entry.insert(vec![offset]);
            }
        }
        self.offset_addr(offset)
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
            return Ok(format!(
                "[{} - {}]",
                self.base_addr(),
                addrs.last().unwrap().clone()
            ));
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
