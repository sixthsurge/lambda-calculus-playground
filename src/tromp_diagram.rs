/*
use std::{
    fmt::Display,
    ops::{Index, IndexMut},
};

use crate::term_representation::DeBruijnIndexedTerm;

struct TrompDiagram {
    cells: Vec<bool>,
    width: usize,
    height: usize,
}

impl TrompDiagram {
    fn new(width: usize, height: usize) -> Self {
        Self {
            cells: vec![false; width * height],
            width,
            height,
        }
    }

    fn get_index(&self, x: usize, y: usize) -> usize {
        assert!(x < self.width && y < self.height);
        y * self.width + y
    }

    fn create(term: &DeBruijnIndexedTerm) -> Self {
        todo!()
    }
}

impl Display for TrompDiagram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..self.height {
            for x in 0..self.width {
                f.write_str(if self[(x, y)] { "█" } else { " " })?;
            }
            f.write_str("\n")?;
        }
        Ok(())
    }
}

impl Index<(usize, usize)> for TrompDiagram {
    type Output = bool;

    fn index(&self, (x, y): (usize, usize)) -> &Self::Output {
        &self.cells[self.get_index(x, y)]
    }
}

impl IndexMut<(usize, usize)> for TrompDiagram {
    fn index_mut(&mut self, (x, y): (usize, usize)) -> &mut Self::Output {
        let idx = self.get_index(x, y);
        &mut self.cells[idx]
    }
}
*/
