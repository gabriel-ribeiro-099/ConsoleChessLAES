package Console;

class BoardMapper {

    public BoardMapper(){

    }

    /*@ public normal_behavior
    @ requires val >= 1 && val <= 8;
    @ ensures (val == 1 ==> \result == 7) &&
              (val == 2 ==> \result == 6) &&
              (val == 3 ==> \result == 5) &&
              (val == 4 ==> \result == 4) &&
              (val == 5 ==> \result == 3) &&
              (val == 6 ==> \result == 2) &&
              (val == 7 ==> \result == 1) &&
              (val == 8 ==> \result == 0);
    @ also
    @ public normal_behavior
    @     requires val < 1 || val > 8;
    @     ensures \result == -1;
    @ pure
    @*/
    public int map(int val){
        switch(val){
            case 1: return 7;
            case 2: return 6;
            case 3: return 5;
            case 4: return 4;
            case 5: return 3;
            case 6: return 2;
            case 7: return 1;
            case 8: return 0;
            default: return -1;
        }
    }

    /*@ public normal_behavior
      @     requires Character.toLowerCase(val) == 'a' ||
      @              Character.toLowerCase(val) == 'b' ||
      @              Character.toLowerCase(val) == 'c' ||
      @              Character.toLowerCase(val) == 'd' ||
      @              Character.toLowerCase(val) == 'e' ||
      @              Character.toLowerCase(val) == 'f' ||
      @              Character.toLowerCase(val) == 'g' ||
      @              Character.toLowerCase(val) == 'h';
      @     ensures (Character.toLowerCase(val) == 'a' ==> \result == 0) &&
      @             (Character.toLowerCase(val) == 'b' ==> \result == 1) &&
      @             (Character.toLowerCase(val) == 'c' ==> \result == 2) &&
      @             (Character.toLowerCase(val) == 'd' ==> \result == 3) &&
      @             (Character.toLowerCase(val) == 'e' ==> \result == 4) &&
      @             (Character.toLowerCase(val) == 'f' ==> \result == 5) &&
      @             (Character.toLowerCase(val) == 'g' ==> \result == 6) &&
      @             (Character.toLowerCase(val) == 'h' ==> \result == 7);
      @ also
      @ public normal_behavior
      @     requires !(Character.toLowerCase(val) == 'a' ||
      @               Character.toLowerCase(val) == 'b' ||
      @               Character.toLowerCase(val) == 'c' ||
      @               Character.toLowerCase(val) == 'd' ||
      @               Character.toLowerCase(val) == 'e' ||
      @               Character.toLowerCase(val) == 'f' ||
      @               Character.toLowerCase(val) == 'g' ||
      @               Character.toLowerCase(val) == 'h');
      @     ensures \result == -1;
      @ pure
      @*/
    public int map(char val){
        switch(Character.toLowerCase(val)){
            case 'a': return 0;
            case 'b': return 1;
            case 'c': return 2;
            case 'd': return 3;
            case 'e': return 4;
            case 'f': return 5;
            case 'g': return 6;
            case 'h': return 7;
            default: return -1;
        }
    }
}