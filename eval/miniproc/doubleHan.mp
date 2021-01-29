pA() {
  try {
    pB();
  } catch {
    pC();
  }
  try {
    pB();
  } catch { }
}

pB() {
  if {
    throw;
  } else { }
}

pC() { }
