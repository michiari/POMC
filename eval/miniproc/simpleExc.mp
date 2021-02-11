pA() {
  try {
    pB();
  } catch {
    pErr();
    pErr();
  }
}

pB() {
  pC();
}

pC() {
  if (*) {
    throw;
  } else {
    pC();
  }
}

pErr() { }
