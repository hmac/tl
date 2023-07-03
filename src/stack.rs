#[derive(Clone, Debug)]
pub struct Stack<T> {
    inner: Vec<T>,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Self { inner: vec![] }
    }

    pub fn push(&mut self, x: T) {
        self.inner.push(x)
    }

    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn to_vec(self) -> Vec<T> {
        self.inner
    }
}

impl<T: Eq> Stack<T> {
    /// Return the index of the first element equal to `x`.
    pub fn find(&self, x: &T) -> Option<usize> {
        for (i, y) in self.inner.iter().enumerate().rev() {
            if x == y {
                return Some(i);
            }
        }
        None
    }
}

impl<T> std::ops::Index<usize> for Stack<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.inner[self.inner.len() - index - 1]
    }
}

impl<'a, T> std::iter::IntoIterator for &'a Stack<T> {
    type Item = &'a T;

    type IntoIter = IntoIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self,
            index: 0,
        }
    }
}

pub struct IntoIter<'a, T> {
    inner: &'a Stack<T>,
    index: usize,
}

impl<'a, T> std::iter::Iterator for IntoIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.index += 1;
        if self.index == self.inner.len() {
            None
        } else {
            Some(&self.inner[self.inner.len() - self.index])
        }
    }
}
