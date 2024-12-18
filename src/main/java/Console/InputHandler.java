package Console;

import Chess.Tuple;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class InputHandler {

    //@ spec_public
    private final static Pattern validMove = Pattern.compile("([a-hA-H][1-8])([-])([a-hA-H][1-8])", Pattern.CASE_INSENSITIVE);

    //@ spec_public
    private final BoardMapper mapper;

    /*@ ensures mapper != null;
      @*/
    public InputHandler(){

        //@ assume BoardMapper.class != null;
        mapper = new BoardMapper();
    }

    // DAQUI PARA CIMA LIMPO

    /*@ requires val != null && val.length() == 2;
      @ requires Character.isLetter(val.charAt(0)) && Character.isDigit(val.charAt(1));
      @ ensures \result != null;
      @ assignable \nothing;
      @*/
    public Tuple parse(String val){
        //@ assume val != null && val.length() == 2;
        //@ assume Character.isLetter(val.charAt(0)) && Character.isDigit(val.charAt(1));
        if (val == null || val.length() != 2 ||
                !Character.isLetter(val.charAt(0)) || !Character.isDigit(val.charAt(1))) {
            throw new IllegalArgumentException("Invalid coordinates: " + val);
        }
        int x = mapper.map(val.charAt(0));
        int y = mapper.map(Integer.parseInt(String.valueOf(val.charAt(1))));

        //@ assume x >= 0 && y >= 0 && x < 8 && y < 8;
        return new Tuple(x, y);
    }


    /*@ requires val != null && isValid(val);
  @ ensures \result != null;
  @*/
    public Tuple getFrom(String val) {
        if (val == null) {
            throw new IllegalArgumentException("Input cannot be null");
        }

        if (!isValid(val)) {
            throw new IllegalArgumentException("Invalid input string: " + val);
        }
        return parse(val);
    }



    /*@ requires val != null && isValid(val);
  @ ensures \result != null;
  @*/
    public Tuple getTo(String val){
        if (val == null) {
            throw new IllegalArgumentException("Input cannot be null");
        }

        if (!isValid(val)) {
            throw new IllegalArgumentException("Invalid input string: " + val);
        }

//        Matcher matcher = validMove.matcher(val);
//        matcher.matches();
//        String coords =  matcher.group(3);

        return parse(val);
    }


    /*@ requires val != null;
     @ ensures \result == validMove.matcher(val).matches();
     @ assignable \nothing;
     @ pure
     @*/
    public boolean isValid(String val) {
        return validMove.pattern().matches(val);
    }

}