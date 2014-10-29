--
-- CREATE_FUNCTION_1
--

CREATE FUNCTION widget_in(cstring)
   RETURNS widget
   AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
   LANGUAGE 'C' STRICT;

CREATE FUNCTION widget_out(widget)
   RETURNS cstring
   AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
   LANGUAGE 'C' STRICT;

CREATE FUNCTION int44in(cstring)
   RETURNS city_budget
   AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
   LANGUAGE 'C' STRICT;

CREATE FUNCTION int44out(city_budget)
   RETURNS cstring
   AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
   LANGUAGE 'C' STRICT;

CREATE FUNCTION check_primary_key ()
	RETURNS trigger
	AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/../../../contrib/spi/refint.so'
	LANGUAGE 'C';

CREATE FUNCTION check_foreign_key ()
	RETURNS trigger
	AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/../../../contrib/spi/refint.so'
	LANGUAGE 'C';

CREATE FUNCTION autoinc ()
	RETURNS trigger
	AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/../../../contrib/spi/autoinc.so'
	LANGUAGE 'C';

CREATE FUNCTION funny_dup17 ()
        RETURNS trigger
        AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
        LANGUAGE 'C';

CREATE FUNCTION ttdummy ()
        RETURNS trigger
        AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
        LANGUAGE 'C';

CREATE FUNCTION set_ttdummy (int4)
        RETURNS int4
        AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
        LANGUAGE 'C' STRICT;

CREATE FUNCTION do_sleep (int4)
        RETURNS void
        AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so'
        LANGUAGE 'C' STRICT;

-- Things that shouldn't work:

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE sql
    AS 'SELECT ''not an integer'';';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE sql
    AS 'not even SQL';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE sql
    AS 'SELECT 1, 2, 3;';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE sql
    AS 'SELECT $2;';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE sql
    AS 'a', 'b';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE c
    AS 'nosuchfile';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE c
    AS '/.automount/genh/h/i2/pidur072/postgresql-8.1.4/src/test/regress/regress.so', 'nosuchsymbol';

CREATE FUNCTION test1 (int) RETURNS int LANGUAGE internal
    AS 'nosuch';
