# Conversion Factor Database

The files in this directory constitute a database of unit definitions and
conversion factors that will ultimately be used to perform this unit converter's
functions. These definitions take the form of one-line "records". Records, and
this database a whole, are intended to be as easy as possible for a human to
populate and maintain; significant post-processing is necessary for the unit
converter to do its job efficiently.

This project makes **no guarantees** about the stability of the format of record
files.

Records live in `.dat` files. The particular `.dat` file a particular record
resides in is not significant, nor is order of records within a `.dat` file.
Records are organized into files by whatever method may hopefully be most
intuitive to a human maintaining the database; roughly, they are organized by
"unit systems" or by whatever purpose the records serve.

A record consists of a series of strings delimited by pipes (U+007C, `|`). The
first string in a record determines the record's "type", identified by a single
Latin capital letter. The record's type determines the number, meanings, and
formats of that record's strings.

```
T | Second string | Cadena tercera | 第四字符串
T |      Leading and trailing whitespace     | is trimmed
T | Internal     whitespace     is     left     as     is
T | | This record has four strings, two of which are empty strings |
T | Naturally, a string cannot contain a pipe character. There is no way to
T | escape a pipe either. This is neither a precisely defined file format, nor
T | a format intended for general use, or indeed, any use besides describing
T | unit conversion factors. It'll be fine.
```

Any part of a line including and following a number sign (U+0023, `#`) is a
comment.

```
# This is a comment
T | This part of the line is not a comment  # But this part is.
T | Turns out, a string can't have a number sign either.
## There is no documentation-generating tool, so it's not exactly relevant, but
## why not, right? Documentation comments start with two number signs.
```

## `Q`-Records: Quantities

A "quantity" is any property that can be quantified by a unit, such as length or
duration or voltage. In the context of this unit converter, it might be more
helpful and more precise to define a quantity as some property shared by units
between whom unit conversion is sensible. This definition does not presuppose
any physicality of quantities; if a set of units can all be converted to and
from each other, then they share a quantity.

A quantity is identified by a mnemonic made up of four Latin capital letters.

```
# | Mnemonic
Q | TIME
```

In the real world, quantities have dimensions. In our world, we're going to
pretend they don't, because implementing dimensional analysis significantly
increases runtime and complexity and requires me to answer difficult questions
about whether it truly makes sense to convert between units of energy and torque
or frequency and angular velocity.

If I'm totally honest, explicitly declaring quantities like this isn't required.
As long as quantities are consistently referred to by the same mnemonics,
everything will play nice. Doing it this way, however, will hopefully reduce the
possibility of typos in the future.

## `R`-Records: Quantity Relations

Sometimes units of one quantity can be converted to units of another quantity. A
"quantity relation" describes the way the reference unit of a source quantity
can be converted to the reference unit of a destination quantity. A special
subroutine, identified by a handler name, performs the relevant computation.

This relation only goes one way. For two-way conversions, the inverse relation
must also be declared.

A blank handler indicates a one-way inheritance.

```
# | Source quantity | Destination quantity | Handler
R | FREQ            | ANGV                 | mul_2pi
R | ANGV            | FREQ                 | div_2pi
R | SRCQ            | DESQ                 |    # SRCQ can be converted to DESQ
                                                # without special code, but the
                                                # reverse conversion cannot.
```

## `S`-Records: Reserved

This section is reserved. In the future, `S`-records will be used to denote
"special" quantities like threads that require special data structures. This
will most likely be indicated with an "extension" in the unit converter.

## `P`-Records: Unit Prefixes

A "unit prefix" is a prefix appended to a unit that affects the magnitude of
that unit; think SI prefixes.

```
# | Prefix | Factor
P | k      | 1e3
P | m      | 1e-3
```

Prefixes are applied to all named units, even if this results in nonconventional
or nonsensical units (millitroy ounces---or would it be troy milliounces?---
kibigallons, nanobytes, etc.).

## `U`-Records: Named Units

A "named unit" is a...unit with a name, as opposed to a unit whose name is
derived from other units. So the newton is an example of a named unit, while the
newton-metre is not.

```
# | Symbol | Annotation | Quantity | Transformation
U | s      |            | TIME     | 1
U | min    |            | TIME     | 60
U | eV/c²  |            | MASS     | 1.78266192e-36
U | gal    | US         | VOLM     | 3.785e-3
U | gal    | Imperial   | ANGL     | 4.546e-3
W | °C     |            | TEMP     | 1 + -273.15
```

A unit's transformation is an affine transformation and is relative to the
reference unit (coherent SI unit or other fitting "natural" unit) of that
particular quantity. Even the radian.

The transformation string is one number or two numbers delimited by a `+`. The
first number (or if there is only one number, the only number) is the magnitude,
and the second number is the offset (or zero if there is only one number).
Offsets must be rational.

There are some considerations when comparing the symbols of named units:

  - Unicode canonical equivalence (e.g. `Ω` U+2126 = `Ω` U+03A9)
  - Unicode compatibility (e.g. `㎓` = `GHz`)
  - Whitespace is ignored (e.g. `oz    t` = `ozt` = `oz t`)
  - Abbreviations are ignored (e.g. `fl. oz.` = `fl oz`)

These principles are designed to introduce the possibility of symbol ambiguity
to facilitate greater user friendliness and to reflect the messiness of the
real-world use of symbols. In such cases of ambiguity, an annotation will be
used to assist in disambiguation.

## `A`-Records: Reserved

This section is reserved. In the future `A`-records may be used to define unit
aliases and perhaps allow for the specification of a "canonical" unit symbol.

## `V`-Records: Unit Schemata

Why did I choose the letter V? 'Cause it looks like a U but isn't one.

Unit schemata allow for the definition of derived units. Any named unit
(including with prefixes) can be used in the schema.

```
# | Schema         | Quantity
V | FORC * LENG    | TORQ
V | LENG^2         | AREA
V | LENG * TIME^-2 | ACCL
```

All units of a particular quantity can be used to define new units in accordance
with the schema, even if this results in unusual system-mixing. Maybe someone
out there needs to convert to pound-metres.

In addition to the considerations necessary for comparing named unit symbols,
there are additional considerations when comparing the symbols of units
generated by unit schemata:

  - Unicode compatibility (e.g. `㎨` = `m∕s2` = `m∕s²`)
  - Notation for multiplication (e.g. `N-m` = `N*m` = `N m` = `Nm` = `N·m`)
  - Notation for division (e.g. `m/s` U+002F = `m∕s` U+2215)
  - Notation for exponentiation (e.g. `m^3` = `m³`)
  - Whitespace for multiplication is ignored (e.g. `kW    h` = `kWh` = `kW h`)
  - Multiplicative commutativity (e.g. `lbf·ft` = `ft·lbf`)
  - Multiplicative inversion

Like with named units, these principles necessarily introduce the possibility of
symbol ambiguity.

## `W`-Records: "Weird" Units

Some units have bizarre properties that must be programmed in for. The unit
converter, upon encountering such a "weird" unit, will shunt the conversion off
to a special subroutine, identified by a handler name, that can handle the unit. 

```
# | Symbol | Annotation | Quantity | Handler
W | hms    |            | TIME     | hms              # Hours, minutes, and seconds
W | ft in  |            | LENG     | ft_in            # Feet and inches

```

## `D`-Records: Reserved

This section is reserved. In the future `D`-records may be used to define a
quantity "designation." These can be converted to units but cannot be prefixed
and cannot be used in unit schemata. Designations may require special notation
and formatting rules (think feet and inches, pounds and ounces, wire gauge,
the possibilities are endless).