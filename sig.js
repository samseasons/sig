a0 = 0, a1 = 1, a16 = 16, a32 = 32, a64 = 64, a160 = 160, a162 = 162, a192 = 192, a15552 = 15552, b0 = 0n, b4 = 4n

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24 >> 0)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 10

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  while (a.length > a64) {
    a = [...expand(a.slice(a0, a64), a0, a32), ...a.slice(a64)]
  }
  return expand(a, a0, h)
}

function bigint (a) {
  let b = b0
  for (let c = 256n, i = a0, l = a.length - a1; i <= l; i++) {
    b += big(a[i]) * c ** big(l - i)
  }
  return b
}

function branches (a) {
  const b = [], c = a * b4 + 1n
  for (let i = b0; i < b4; i++) {
    b.push(c + i)
  }
  return b
}

function root (a) {
  return big((a - 1n) / b4)
}

function trits (a) {
  a = bigint(a)
  let b = 3n, c = a0, d = a162, e = uint8(d)
  while (c < d) {
    e[--d] = num(a % b)
    a /= b
  }
  return e
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

function gen (a=randombytes(a32)) {
  a = expand(a, a0, a15552)
  const c = uint8(a15552)
  for (let i = a0, j = a0, k, l; i < a162; i++) {
    k = j + a32
    l = k + a32
    c.set(expand(a.slice(j, k), a0, a32), j)
    c.set(expand(a.slice(k, l), a0, a32), k)
    j = l + a32
    c.set(expand(a.slice(l, j), a0, a32), l)
  }
  return reduce(c, a32)
}

function sign (a, b) {
  a = trits(a)
  const c = uint8(a32 + a15552), d = uint8(a15552), e = expand(b, a0, a15552)
  for (let i = a0, j, k, l, m = a0; i < a162; i++) {
    j = m
    k = j + a32
    l = k + a32
    m = l + a32
    d.set(expand(e.slice(j, k), a0, a32), j)
    d.set(expand(e.slice(k, l), a0, a32), k)
    d.set(expand(e.slice(l, m), a0, a32), l)
    if (a[i] == a0) {
      c.set(e.slice(j, k), k)
      c.set(d.slice(k, l), l)
      c.set(d.slice(l, m), m)
    } else if (a[i] == a1) {
      c.set(d.slice(j, k), k)
      c.set(e.slice(k, l), l)
      c.set(d.slice(l, m), m)
    } else {
      c.set(d.slice(j, k), k)
      c.set(d.slice(k, l), l)
      c.set(e.slice(l, m), m)
    }
  }
  c.set(reduce(d, a32))
  return c
}

function valid (a, b, c) {
  if (b.length != a32) {
    return false
  }
  a = trits(a)
  const d = uint8(a15552)
  for (let i = a0, j, k, l, m = a0; i < a162; i++) {
    j = m
    k = j + a32
    l = k + a32
    if (a[i] == a0) {
      d.set(expand(c.slice(j, k), a0, a32), j)
      d.set(c.slice(k, l), k)
      d.set(c.slice(l, m = l + a32), l)
    } else if (a[i] == a1) {
      d.set(c.slice(j, k), j)
      d.set(expand(c.slice(k, l), a0, a32), k)
      d.set(c.slice(l, m = l + a32), l)
    } else {
      d.set(c.slice(j, k), j)
      d.set(c.slice(k, l), k)
      d.set(expand(c.slice(l, m = l + a32), a0, a32), l)
    }
  }
  return b.toString() == reduce(d, a32).toString()
}

function sig (a, b, c=a0) {
  if (typeof c == 'number') {
    c = big(c)
  } else if (typeof c == 'object') {
    if (c.length > a32) {
      c = reduce(c, a32)
    }
    c = bigint(c)
  }
  const f = [c]
  while (c > b0) {
    f.unshift(c = root(c))
  }
  let e, g, h, i, j, k
  const o = 32n, p = 64n
  g = branches(f[f.length - a1])
  h = g[g.length - a1] * p
  b = reduce(b, a32)
  c = [...b]
  c.push(...sign(b, expand(a, h + o, h + p)))
  const d = [], r = {}, s = {}
  for (i in f.reverse()) {
    g = f[i]
    h = g * p
    if (!(g in r)) {
      r[g] = expand(a, h, h + o)
    }
    e = branches(g)
    for (i of e) {
      if (!(i in s)) {
        h = i * p
        r[i] = expand(a, h, h + o)
        s[i] = gen(r[i])
      }
    }
    h = [...gen(expand(a, h + o, h + p))]
    j = a0
    k = num(b4)
    while (j < k) {
      h.push(...s[e[j++]])
    }
    j = sign(reduce(h, a32), r[g])
    s[g] = j.slice(a0, a32)
    d.unshift(...j)
    d.unshift(...h)
  }
  c.push(...d)
  return c
}

function verify (a, b, c) {
  try {
    a = reduce(a, a32)
    if (c.slice(a0, a32).toString() != a.toString()) {
      console.log('bad match', a, c.slice(a0, a32))
      return false
    }
    const d = c.slice(a32, a64)
    c = c.slice(a64)
    let e, f, g, j, s = c.slice(a0, a15552)
    c = c.slice(a15552)
    if (!valid(a, d, s)) {
      console.log('bad first', a, d, s)
      return false
    }
    if (c.slice(a160, a192).toString() != b.toString()) {
      console.log('bad public', b, c.slice(a160, a192))
      return false
    }
    const l = c.length / (a192 + a15552)
    if (l % a1 != a0) {
      console.log('bad length', c.length, l)
      return false
    }
    i = a0
    while (i < l) {
      e = c.slice(a160, a192)
      if (i++ > a0) {
        b = false
        f = e.toString()
        j = a0
        while (j < a160) {
          if (g.slice(j, j += a32).toString() == f) {
            b = true
          }
        }
        if (!b) {
          console.log('bad sign', a, e, s)
          return false
        }
      }
      g = c.slice(a0, a160)
      c = c.slice(a192)
      s = c.slice(a0, a15552)
      c = c.slice(a15552)
      if (!valid(reduce(g, a32), e, s)) {
        console.log('bad branch', e, reduce(g, a32), s)
        return false
      }
    }
    b = false
    f = d.toString()
    j = a0
    while (j < a160) {
      if (g.slice(j, j += a32).toString() == f) {
        b = true
      }
    }
    if (b) {
      return true
    }
    console.log('bad last', f)
  } catch (e) {
    console.log('error', e)
  }
  return false
}

data = randombytes(a32)
priv = randombytes(a32)
pub = gen(expand(priv, a0, a32))
signature = sig(priv, data)
verify(data, pub, signature)