a0 = 0, a1 = 1, a2 = 2, a5 = 5, a16 = 16, a32 = 32, a64 = 64, a160 = 160, a192 = 192, a16384 = 16384, b0 = 0n, b4 = 4n

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
  g = BigInt(g)
  h = BigInt(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a16] | a0)
      j = uint32(a16).map((c, b) => a[b + a32] | a0)
  a = uint8(Number(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + 1
    a[c] = h + 1
    a[d] = i + 1
    a[e] = j + 1
  }

  function l () {
    let a = i.slice(), b = i.slice(), c, d = 16, e = 25

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
      if (e % a5 == a0) {
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
    let b = b0, c = a0, d = a16
    while (c < d) {
      b = b * m + BigInt(a[c++])
    }
    return b
  }

  function o (a, b) {
    let c = 15, d = a0
    while (c > d) {
      b[c--] = Number(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(Number(m), Number(m + h - g)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, Number(h - b)), Number(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  let b, c = a.length, d
  while (c > a32) {
    b = []
    while (c > a0) {
      d = c / a2
      b.push(...expand([...a.slice(a0, a32), ...a.slice(d, d + a32)], a0, a32))
      a = [...a.slice(a32, d), ...a.slice(d + a32)]
      c = a.length
    }
    a = b.slice()
    c = a.length
  }
  return expand(a, a0, h)
}

function bigint (a) {
  let b = b0, c = 256n, l = a.length - a1
  for (let i = l; i >= a0; i--) {
    b += BigInt(a[i]) * (c ** BigInt(l - i))
  }
  return b
}

function root (a) {
  return BigInt((a - 1n) / b4)
}

function branches (a) {
  const b = []
  let c = a * b4 + 1n
  for (let i = b0; i < b4; i++) {
    b.push(c + i)
  }
  return b
}

function strbits (a) {
  return ('00000000' + a.toString(a2)).substr(-8)
}

function bytebits (a) {
  a = strbits(a).split('')
  const b = []
  for (let i = a.length - a1; i >= a0; i--) {
    b.push(parseInt(a[i]))
  }
  return b
}

function bits (a) {
  const b = []
  for (let i = a0, l = a.length; i < l; i++) {
    b.push(...bytebits((a[i])))
  }
  return b
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

function gen (a=randombytes(a32)) {
  a = expand(a, a0, a16384 + a64)
  const c = uint8(a16384)
  for (let i = a0, j, k, l = 256; i < l; i++) {
    j = i * a64
    k = j + a32
    c.set(expand(a.slice(j, k), a0, a32), j)
    c.set(expand(a.slice(k, k + a32), a0, a32), k)
  }
  return reduce(c, a32)
}

function sign (a, b) {
  a = bits(a)
  const c = uint8(a16384), d = uint8(a16384)
  const e = expand(b, a0, a16384 + a64)
  b = uint8(a16384 + a32)
  for (let i = a0, j, k, l = 256; i < l; i++) {
    j = i * a64
    k = j + a32
    d.set(expand(e.slice(j, k), a0, a32), j)
    d.set(expand(e.slice(k, k + a32), a0, a32), k)
    if (a[i]) {
      c.set(d.slice(j, k), j)
      c.set(e.slice(k, k + a32), k)
    } else {
      c.set(e.slice(j, k), j)
      c.set(d.slice(k, k + a32), k)
    }
  }
  b.set(reduce(d, a32))
  b.set(c, a32)
  return b
}

function valid (a, b, c) {
  if (b.length != a32) {
    return false
  }
  a = bits(a)
  const d = uint8(a16384)
  for (let i = a0, j, k, l = a.length; i < l; i++) {
    j = i * a64
    k = j + a32
    if (a[i]) {
      d.set(c.slice(j, k), j)
      d.set(expand(c.slice(k, k + a32), a0, a32), j + a32)
    } else {
      d.set(expand(c.slice(j, k), a0, a32), j)
      d.set(c.slice(k, k + a32), j + a32)
    }
  }
  return reduce(d, a32).toString() == b.toString()
}

function sig (a, b, c=a0) {
  if (typeof c == 'number') {
    c = BigInt(c)
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
  let p = 64n, q = p / 2n
  const r = {}, s = {}
  h = branches(f[f.length - a1])
  g = p * h[h.length - a1]
  a = reduce(a, a32)
  c = [...a]
  c.push(...sign(a, expand(b, g + q, g + p)))
  const d = []
  for (i in f.reverse()) {
    h = f[i]
    g = p * h
    if (!(h in r)) {
      r[h] = expand(b, g, g + q)
    }
    e = branches(h)
    e.filter(i => {
      if (!(i in s)) {
        g = p * i
        r[i] = expand(b, g, g + q) 
        s[i] = gen(r[i])
      }
    })
    g = [...gen(expand(b, g + q, g + p))]
    j = a0
    k = Number(b4)
    while (j < k) {
      g.push(...s[e[j++]])
    }
    j = sign(reduce(g, a32), r[h])
    s[h] = j.slice(a0, a32)
    d.unshift(...j)
    d.unshift(...g)
  }
  c.push(...d)
  return c
}

function verify (a, b, c) {
  try {
    a = reduce(a, a32)
    if (c.slice(a0, a32).toString() != a.toString()) {
      console.log('bad match', c.slice(a0, a32), a)
      return false
    }
    c = c.slice(a32)
    const g = c.slice(a0, a32)
    c = c.slice(a32)
    let d, e, f, j, k, s = c.slice(a0, a16384)
    c = c.slice(a16384)
    if (!valid(a, g, s)) {
      console.log('bad first', g, a, s)
      return false
    }
    if (c.slice(a160, a192).toString() != b.toString()) {
      console.log('bad public', b, c.slice(a160, a192))
      return false
    }
    const l = c.length / (a16384 + a192)
    if (l % a1 != a0) {
      console.log('bad length', c.length, l)
    }
    for (let i = a0; i < l; i++) {
      d = c.slice(a160, a192)
      if (i > a0) {
        b = false
        f = d.toString()
        for (j = a0; j < a5; j++) {
          k = j * a32
          if (e.slice(k, k + a32).toString() == f) {
            b = true
          }
        }
        if (!b) {
          console.log('bad sign', i, d, a, s)
          return false
        }
      }
      e = c.slice(a0, a160)
      c = c.slice(a192)
      s = c.slice(a0, a16384)
      c = c.slice(a16384)
      if (!valid(reduce(e, a32), d, s)) {
        console.log('bad branch', i, d, reduce(e, a32), s)
        return false
      }
    }
    b = false
    f = g.toString()
    for (j = a0; j < a5; j++) {
      k = j * a32
      if (e.slice(k, k + a32).toString() == f) {
        b = true
      }
    }
    if (!b) {
      console.log('bad last', d, data, si)
      return false
    } else {
      return true
    }
  } catch (e) {
    console.log('error', e)
    return false
  }
}

data = randombytes(a32)
priv = randombytes(a32)
pub = gen(expand(priv, a0, a32))
signature = sig(data, priv)
verify(data, pub, signature)