var foo;

pA() {
  foo = false;
  try {
    pB();
  } catch {
    pC();
  }
}

pB() {
  if (foo) {
    throw;
  } else {}
}

pC() { }
